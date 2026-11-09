open Config
open Ty
open Ctx
open Env

(* An operation of [module_] on [location]. Atomic.Array has no incr or decr,
   so it passes [~counters:false]. *)
let atomic_op ?(module_ = "Atomic") ?(counters = true) ctx env location ty expr =
  (* Let-bound because argument evaluation order is unspecified and differs
     between ocamlc and ocamlopt. *)
  let compare_and_set seen value =
    let expected = fresh ctx "c"
    and desired = fresh ctx "c" in
    [%string
      "(let %{expected} = %{seen} in let %{desired} = %{value} in \
       %{module_}.compare_and_set %{location} %{expected} %{desired})"]
  in
  (* Keeps the old value live, so it may be spilled. *)
  let keep_old op value =
    let old = fresh ctx "old" in
    let use_old = expr (bind env old ty) ty in
    [%string
      "(let %{old} = %{op} %{location} %{value} in ignore (Sys.opaque_identity \
       %{use_old}))"]
  in
  let get = [%string "%{module_}.get %{location}"] in
  choose
    ctx
    ([ (fun () -> [%string "%{module_}.set %{location} %{expr env ty}"])
     ; (fun () -> [%string "ignore (%{module_}.exchange %{location} %{expr env ty})"])
     ; (fun () -> keep_old (module_ ^ ".exchange") (expr env ty))
     ; (fun () -> [%string "ignore %{compare_and_set get (expr env ty)}"])
     ; (fun () -> [%string "ignore %{compare_and_set (expr env ty) (expr env ty)}"])
     ; (fun () ->
         Printf.sprintf
           "(if %s then %s)"
           (compare_and_set (expr env ty) (expr env ty))
           (match ty with
            | Int when counters -> [%string "%{module_}.incr %{location}"]
            | Int -> [%string "%{module_}.set %{location} (%{get} + 1)"]
            | _ -> [%string "%{module_}.set %{location} (not (%{get}))"]))
     ]
     @
     match ty with
     | Int ->
       [ (fun () ->
           [%string "ignore (%{module_}.fetch_and_add %{location} %{expr env Int})"])
       ; (fun () -> keep_old (module_ ^ ".fetch_and_add") (expr env Int))
       ]
       @
       if counters
       then
         [ (fun () -> [%string "%{module_}.incr %{location}"])
         ; (fun () -> [%string "%{module_}.decr %{location}"])
         ]
       else []
     | _ -> [])
;;

(* Atomics hold an int or a bool, so compare_and_set's physical equality behaves the same
   on every backend. *)
let local_atomic ctx env ty expr =
  let atomic = fresh ctx "at" in
  let loop_var = fresh ctx "i" in
  let body = bind (bind env [%string "(Atomic.get %{atomic})"] ty) loop_var Int in
  let operations =
    List.init (int_in ctx 1 3) (fun _ -> atomic_op ctx body atomic ty expr)
  in
  let operations = String.concat "; " operations in
  [%string
    "(let %{atomic} = Atomic.make %{expr env ty} in for %{loop_var} = 0 to (%{expr env \
     Int} land 7) do %{operations} done; Atomic.get %{atomic})"]
;;

(* A record with atomic fields (declared in the prelude), updated through
   atomic locations and plain writes. *)
let atomic_fields ctx env ty expr =
  let record = fresh ctx "ar" in
  let loop_var = fresh ctx "i" in
  let field = if ty = Int then "ai" else "ab" in
  let location = [%string "[%atomic.loc %{record}.%{field}]"] in
  let body =
    bind
      (bind
         (bind env [%string "(Atomic.Loc.get %{location})"] ty)
         [%string "%{record}.%{field}"]
         ty)
      loop_var
      Int
  in
  let operation () =
    choose
      ctx
      [ (fun () -> atomic_op ~module_:"Atomic.Loc" ctx body location ty expr)
      ; (fun () -> [%string "%{record}.%{field} <- %{expr body ty}"])
      ; (fun () -> [%string "%{record}.ap <- %{expr body Int}"])
      ]
  in
  let operations =
    String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> operation ()))
  in
  let ap = expr env Int in
  let ab = expr env Bool in
  let ai = expr env Int in
  [%string
    "(let %{record} = { ai = %{ai}; ab = %{ab}; ap = %{ap} } in for %{loop_var} = 0 to \
     (%{expr env Int} land 7) do %{operations} done; Atomic.Loc.get %{location})"]
;;

(* An atomic array of four ints, at indices kept in bounds. *)
let atomic_array ctx env expr =
  let array = fresh ctx "aa" in
  let loop_var = fresh ctx "i" in
  let body = bind (bind env [%string "(Atomic.Array.get %{array} 0)"] Int) loop_var Int in
  let operation () =
    let index = [%string "((%{expr body Int}) land 3)"] in
    atomic_op
      ~module_:"Atomic.Array"
      ~counters:false
      ctx
      body
      [%string "%{array} %{index}"]
      Int
      expr
  in
  let operations =
    String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> operation ()))
  in
  let init = expr env Int in
  [%string
    "(let %{array} = Atomic.Array.make 4 %{init} in for %{loop_var} = 0 to (%{expr env \
     Int} land 7) do %{operations} done; Atomic.Array.get %{array} (%{expr env Int} land \
     3))"]
;;

let forms ctx env ty gen =
  let expr = gen.expr in
  boost
    (if immediate ty && on "atomics"
     then [ (fun () -> local_atomic ctx env ty expr) ]
     else [])
  @ (if immediate ty && on "atomics" && has "atomic_loc"
     then [ (fun () -> atomic_fields ctx env ty expr) ]
     else [])
  @
  if ty = Int && on "atomics" && has "atomic_array"
  then [ (fun () -> atomic_array ctx env expr) ]
  else []
;;
