open Config
open Ty
open Ctx
open Env

(* An operation on the atomic [location]. *)
let atomic_op ctx env location ty expr =
  (* Let-bound because argument evaluation order is unspecified and differs
     between ocamlc and ocamlopt. *)
  let compare_and_set seen value =
    let expected = fresh ctx "c"
    and desired = fresh ctx "c" in
    [%string
      "(let %{expected} = %{seen} in let %{desired} = %{value} in Atomic.compare_and_set \
       %{location} %{expected} %{desired})"]
  in
  (* Keeps the old value live, so it may be spilled. *)
  let keep_old op value =
    let old = fresh ctx "old" in
    let use_old = expr (bind env old ty) ty in
    [%string
      "(let %{old} = %{op} %{location} %{value} in ignore (Sys.opaque_identity \
       %{use_old}))"]
  in
  let get = [%string "Atomic.get %{location}"] in
  choose
    ctx
    ([ (fun () -> [%string "Atomic.set %{location} %{expr env ty}"])
     ; (fun () -> [%string "ignore (Atomic.exchange %{location} %{expr env ty})"])
     ; (fun () -> keep_old "Atomic.exchange" (expr env ty))
     ; (fun () -> [%string "ignore %{compare_and_set get (expr env ty)}"])
     ; (fun () -> [%string "ignore %{compare_and_set (expr env ty) (expr env ty)}"])
     ; (fun () ->
         Printf.sprintf
           "(if %s then %s)"
           (compare_and_set (expr env ty) (expr env ty))
           (match ty with
            | Int -> [%string "Atomic.incr %{location}"]
            | _ -> [%string "Atomic.set %{location} (not (%{get}))"]))
     ]
     @
     match ty with
     | Int ->
       [ (fun () -> [%string "ignore (Atomic.fetch_and_add %{location} %{expr env Int})"])
       ; (fun () -> keep_old "Atomic.fetch_and_add" (expr env Int))
       ]
       @ [ (fun () -> [%string "Atomic.incr %{location}"])
         ; (fun () -> [%string "Atomic.decr %{location}"])
         ]
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

let forms ctx env ty gen =
  let expr = gen.expr in
  boost
    (if immediate ty && on "atomics"
     then [ (fun () -> local_atomic ctx env ty expr) ]
     else [])
;;
