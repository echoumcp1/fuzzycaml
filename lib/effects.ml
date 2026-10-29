open Ty
open Ctx
open Env

(* The effects a handler handles, the type [b] of its body, whether it
   catches Exit, and the body's environment. *)
let handler_setup ctx env =
  let handled = List.filter (fun _ -> flip ctx) ctx.effects in
  let handled = if handled = [] then [ List.hd ctx.effects ] else handled in
  let b =
    from_env
      ctx
      { env with vars = List.map (fun (c, _, r) -> c, r) handled }
      some_ty
      (fun () -> fo_env_ty ctx env)
  in
  let catch = flip ~p:0.3 ctx in
  handled, b, catch, { env with effs = handled @ env.effs; in_try = env.in_try || catch }
;;

(* A handler arm for an effect with argument [a] and result [r]. It resumes the
   body, resumes it and uses the result, drops the continuation, or (inside a
   try, if [discontinue]) raises Exit at the perform. *)
let arm ctx env ty e ~resume ~discontinue (_, a, r) =
  let v = fresh ctx "v" in
  let k = fresh ctx "k" in
  let henv = bind env v a in
  let res = fresh ctx "r" in
  let resumed () = resume k (e henv r) r in
  ( v
  , k
  , choose
      ctx
      ([ resumed
       ; (fun () ->
           [%string "(let %{res} : %{show_ty ty} = %{resumed ()} in %{e (bind henv res ty) ty})"])
       ; (fun () -> [%string "(ignore %{k}; %{e henv ty})"])
       ]
       @
       if discontinue && env.in_try
       then [ (fun () -> [%string "Effect.Deep.discontinue %{k} Exit"]) ]
       else []) )
;;

let deep_resume k v r = [%string "Effect.Deep.continue %{k} (%{v} : %{show_ty r})"]

(* A handler's exnc: it catches Exit if [catch]. *)
let exnc env ty e catch =
  if catch then [%string "(function Exit -> %{e env ty} | ex -> raise ex)"] else "raise"
;;

(* Performs [c] with an argument of type [a] and binds its result of type [r]
   in a body of type [ty]. *)
let perform_let ctx env e (c, a, r) ty =
  let y = fresh ctx "y" in
  [%string "(let %{y} : %{show_ty r} = Effect.perform (%{c} %{e env a}) in %{e (bind env y r) ty})"]
;;

(* A deep handler for some of the program's effects around a body of type [b]. *)
let handler ctx env ty e =
  let handled, b, catch, body_env = handler_setup ctx env in
  let x = fresh ctx "x" in
  let exnc = exnc env ty e catch in
  let arm ((c, _, _) as eff) =
    let v, k, body = arm ctx env ty e ~resume:deep_resume ~discontinue:true eff in
    [%string "| %{c} %{v} -> Some (fun (%{k} : (a, %{show_ty ty}) Effect.Deep.continuation) -> %{body})"]
  in
  p
    "(Effect.Deep.match_with (fun () -> %s) () { Effect.Deep.retc = (fun (%s : %s) -> \
     %s); exnc = %s; effc = (fun (type a) (eff : a Effect.t) -> match eff with %s | _ \
     -> None) })"
    (let eff = pick ctx handled in
     if flip ctx then perform_let ctx body_env e eff b else e body_env b)
    x
    (show_ty b)
    (e (bind env x b) ty)
    exnc
    (String.concat " " (List.map arm handled))
;;

(* A shallow handler. [go] resumes the fiber under the same handler each time.
   *)
let shallow ctx env ty e =
  let handled, b, catch, body_env = handler_setup ctx env in
  let go = fresh ctx "go" in
  let tv = fresh ctx "c" in
  let x = fresh ctx "x" in
  let exnc = exnc env ty e catch in
  let arm ((c, _, _) as eff) =
    let resume k v _ = [%string "%{go} %{k} %{v}"] in
    let v, k, body = arm ctx env ty e ~resume ~discontinue:false eff in
    [%string "| %{c} %{v} -> Some (fun (%{k} : (a, %{show_ty b}) Effect.Shallow.continuation) -> %{body})"]
  in
  p
    "(let rec %s : type %s. (%s, %s) Effect.Shallow.continuation -> %s -> %s = fun k v \
     -> Effect.Shallow.continue_with k v { Effect.Shallow.retc = (fun (%s : %s) -> %s); \
     exnc = %s; effc = (fun (type a) (eff : a Effect.t) -> match eff with %s | _ -> \
     None) } in %s (Effect.Shallow.fiber (fun () -> %s)) ())"
    go
    tv
    tv
    (show_ty b)
    tv
    (show_ty ty)
    x
    (show_ty b)
    (e (bind env x b) ty)
    exnc
    (String.concat " " (List.map arm handled))
    go
    (e body_env b)
;;

(* OCaml 5.3's [match ... with effect E v, k -> ...]. *)
let effect_match ctx env ty e =
  let handled, b, catch, body_env = handler_setup ctx env in
  let x = fresh ctx "x" in
  let arm ((c, _, _) as eff) =
    let v, k, body = arm ctx env ty e ~resume:deep_resume ~discontinue:true eff in
    [%string "| effect %{c} %{v}, %{k} -> %{body}"]
  in
  p
    "(match %s with | %s -> %s %s%s)"
    (e body_env b)
    x
    (e (bind env x b) ty)
    (String.concat " " (List.map arm handled))
    (if catch then [%string " | exception Exit -> %{e env ty}"] else "")
;;
