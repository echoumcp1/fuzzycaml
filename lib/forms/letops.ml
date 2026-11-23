open Config
open Ty
open Ctx
open Gen_ty
open Env

type monad =
  | Option_like
  | Result_like
  | State
  | Writer
  | Continuation
  | Identity

type operators =
  { bind : string
  ; map : string
  ; product : string
  }

(* Operators that use [captured] are closures, which the compiler cannot
   inline as freely. *)
let operators monad captured =
  match monad with
  | Option_like ->
    { bind =
        (match captured with
         | Some c ->
           [%string "m f = match m with Some x when %{c} land 7 <> 0 -> f x | _ -> None"]
         | None -> "m f = match m with Some x -> f x | None -> None")
    ; map = "m f = match m with Some x -> Some (f x) | None -> None"
    ; product = "a b = match a, b with Some x, Some y -> Some (x, y) | _ -> None"
    }
  | Result_like ->
    let error =
      match captured with
      | Some c -> [%string "Error (e + %{c})"]
      | None -> "Error e"
    in
    { bind = [%string "m f = match m with Ok x -> f x | Error e -> %{error}"]
    ; map = "m f = match m with Ok x -> Ok (f x) | Error e -> Error e"
    ; product =
        "a b = match a, b with Ok x, Ok y -> Ok (x, y) | Error e, _ | _, Error e -> \
         Error e"
    }
  | State ->
    let next =
      match captured with
      | Some c -> [%string "(s + %{c})"]
      | None -> "s"
    in
    { bind = [%string "m f = fun s -> let (x, s) = m s in f x %{next}"]
    ; map = "m f = fun s -> let (x, s) = m s in (f x, s)"
    ; product = "a b = fun s -> let (x, s) = a s in let (y, s) = b s in ((x, y), s)"
    }
  | Writer ->
    let log =
      match captured with
      | Some c -> [%string "w + v + %{c}"]
      | None -> "w + v"
    in
    { bind = [%string "(x, w) f = let (y, v) = f x in (y, %{log})"]
    ; map = "(x, w) f = (f x, w)"
    ; product = "(x, w) (y, v) = ((x, y), w + v)"
    }
  | Continuation ->
    { bind = "m f = fun k -> m (fun x -> f x k)"
    ; map = "m f = fun k -> m (fun x -> k (f x))"
    ; product = "a b = fun k -> a (fun x -> b (fun y -> k (x, y)))"
    }
  | Identity -> { bind = "x f = f x"; map = "x f = f x"; product = "a b = (a, b)" }
;;

let definitions ctx monad captured =
  let attr = pick ctx [ ""; "[@inline]"; "[@inline never]" ] in
  let { bind; map; product } = operators monad captured in
  let define name body = [%string "let%{attr} ( %{name} ) %{body}"] in
  let defs =
    [ define "let*" bind
    ; define "and*" product
    ; define "let+" map
    ; define "and+" product
    ]
  in
  if flip ctx
  then (
    let joined = String.concat " " defs in
    [%string "let open struct %{joined} end in "])
  else String.concat "" (List.map (fun def -> def ^ " in ") defs)
;;

(* A monadic value holding a [value_ty] made from a generated expression. Only
   [Continuation] needs [final], the type its continuations return. *)
let lift ctx env gen monad ~final value_ty =
  let expr = gen.expr in
  let value () = expr env value_ty in
  match monad with
  | Option_like ->
    choose
      ctx
      [ (fun () -> [%string "(Some (%{value ()}))"])
      ; (fun () ->
          let condition = expr env Bool in
          [%string "(if %{condition} then Some (%{value ()}) else None)"])
      ; (fun () -> [%string "(%{expr env (Option value_ty)})"])
      ]
  | Result_like ->
    choose
      ctx
      [ (fun () -> [%string "(Ok (%{value ()}))"])
      ; (fun () ->
          let condition = expr env Bool in
          let ok = value () in
          [%string
            "(if %{condition} then Ok (%{ok}) else Error %{paren (Literal.literal ctx \
             Int)})"])
      ]
  | State ->
    let v = fresh ctx "v" in
    let s = fresh ctx "s" in
    choose
      ctx
      [ (fun () ->
          let bound = value () in
          let step = int_in ctx 0 9 in
          [%string
            "(let %{v} = %{bound} in fun (%{s} : int) -> (%{v}, %{s} + %{step#Int}))"])
      ; (fun () ->
          let read = expr (bind (closure env) s Int) value_ty in
          let step = int_in ctx 0 9 in
          [%string "(fun (%{s} : int) -> ((%{read}), %{s} * 3 + %{step#Int}))"])
      ]
  | Writer ->
    let v = fresh ctx "v" in
    let w = fresh ctx "w" in
    choose
      ctx
      [ (fun () ->
          let bound = value () in
          [%string "((%{bound}), %{int_in ctx 0 9#Int})"])
      ; (fun () ->
          let bound = value () in
          let log = expr env Int in
          [%string "(let %{v} = %{bound} in let %{w} = %{log} in (%{v}, %{w}))"])
      ]
  | Continuation ->
    let v = fresh ctx "v" in
    let k = fresh ctx "k" in
    choose
      ctx
      [ (fun () ->
          let bound = value () in
          [%string "(let %{v} = %{bound} in fun %{k} -> %{k} %{v})"])
      ; (fun () ->
          let condition = expr env Bool in
          let abort = expr (closure env) final in
          let bound = value () in
          [%string
            "(if %{condition} then (fun (_ : %{value_ty#Ty} -> %{final#Ty}) -> %{abort}) \
             else let %{v} = %{bound} in fun %{k} -> %{k} %{v})"])
      ]
  | Identity -> [%string "(%{value ()})"]
;;

(* Groups of [let*] or [let+] bindings joined by [and*] or [and+]. The arguments
   of an [and] operator are evaluated in an unspecified order, so every right-hand
   side after a group's first is pure. *)
let rec chain ctx env gen monad ~final groups =
  let applicative = groups = 1 && flip ~p:0.3 ctx in
  let keyword, conjunction = if applicative then "let+", "and+" else "let*", "and*" in
  let values = candidates ctx env (fun t -> if restricted t then None else Some t) in
  let bindings =
    List.init (int_in ctx 1 3) (fun i ->
      let rhs_env = if i = 0 then env else pure env in
      let var_ty = draw_ty ctx ~candidates:values (Any value_types) in
      let var = fresh ctx "x" in
      let rhs = lift ctx rhs_env gen monad ~final var_ty in
      var, var_ty, rhs)
  in
  let body_env =
    bind_all (closure env) (List.map (fun (var, var_ty, _) -> var, var_ty) bindings)
  in
  let body =
    if groups > 1
    then chain ctx body_env gen monad ~final (groups - 1)
    else if applicative
    then gen.expr body_env final
    else lift ctx body_env gen monad ~final final
  in
  let binding i (var, var_ty, rhs) =
    let op = if i = 0 then keyword else conjunction in
    [%string "%{op} (%{var} : %{var_ty#Ty}) = %{rhs}"]
  in
  let joined = String.concat " " (List.mapi binding bindings) in
  [%string "%{joined} in %{body}"]
;;

let run ctx env gen monad ty m =
  let expr = gen.expr in
  match monad with
  | Option_like ->
    let v = fresh ctx "v" in
    [%string "(match %{m} with Some %{v} -> %{v} | None -> %{expr env ty})"]
  | Result_like ->
    let v = fresh ctx "v" in
    let e = fresh ctx "e" in
    [%string
      "(match %{m} with Ok %{v} -> %{v} | Error %{e} -> %{expr (bind env e Int) ty})"]
  | State ->
    let start = fresh ctx "s" in
    let v = fresh ctx "v" in
    let s = fresh ctx "s" in
    let init = expr env Int in
    let result = expr (bind (bind env v ty) s Int) ty in
    [%string "(let %{start} = %{init} in let (%{v}, %{s}) = %{m} %{start} in %{result})"]
  | Writer ->
    let v = fresh ctx "v" in
    let w = fresh ctx "w" in
    [%string "(let (%{v}, %{w}) = %{m} in %{expr (bind (bind env v ty) w Int) ty})"]
  | Continuation ->
    let v = fresh ctx "v" in
    [%string "(%{m} (fun (%{v} : %{ty#Ty}) -> %{expr (bind (closure env) v ty) ty}))"]
  | Identity -> m
;;

let letops ctx env ty gen =
  let monad =
    pick ctx [ Option_like; Result_like; State; Writer; Continuation; Identity ]
  in
  let capture =
    match monad with
    | Option_like | Result_like | State | Writer -> flip ctx
    | Continuation | Identity -> false
  in
  let captured_value = if capture then Some (gen.expr env Int) else None in
  let c = fresh ctx "c" in
  let captured = Option.map (fun _ -> c) captured_value in
  let defs = definitions ctx monad captured in
  let m = fresh ctx "m" in
  let chain = chain ctx env gen monad ~final:ty (int_in ctx 1 3) in
  let run = run ctx env gen monad ty m in
  let capture =
    match captured_value with
    | Some value -> [%string "let %{c} : int = %{value} in "]
    | None -> ""
  in
  [%string "(%{capture}%{defs}let %{m} = %{chain} in (%{run} : %{ty#Ty}))"]
;;

let forms ctx env ty gen =
  boost
    (if (not (restricted ty)) && on "letops"
     then [ (fun () -> letops ctx env ty gen) ]
     else [])
;;
