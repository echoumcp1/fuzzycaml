open Hegel
open Ty
open Ctx
open Env

(* The effects a handler handles, the type [b] of its body, whether it
   catches Exit, and the body's environment. *)
let handler_setup ctx env =
  let handled = List.filter (fun _ -> draw_silent ctx.tc (booleans ())) ctx.effects in
  let handled = if handled = [] then [ List.hd ctx.effects ] else handled in
  let b =
    from_env
      ctx
      { env with vars = List.map (fun (c, _, r) -> c, r) handled }
      some_ty
      (fun () -> fo_env_ty ctx env)
  in
  let catch = draw_silent ctx.tc (booleans ~p:0.3 ()) in
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
           p "(let %s : %s = %s in %s)" res (show_ty ty) (resumed ()) (e (bind henv res ty) ty))
       ; (fun () -> p "(ignore %s; %s)" k (e henv ty))
       ]
       @
       if discontinue && env.in_try
       then [ (fun () -> p "Effect.Deep.discontinue %s Exit" k) ]
       else []) )
;;

let deep_resume k v r = p "Effect.Deep.continue %s (%s : %s)" k v (show_ty r)
;;

(* A deep handler for some of the program's effects around a body of type [b]. *)
let handler ctx env ty e =
  let handled, b, catch, body_env = handler_setup ctx env in
  let x = fresh ctx "x" in
  let exnc =
    if catch
    then p "(function Exit -> %s | ex -> raise ex)" (e env ty)
    else "raise"
  in
  let arm ((c, _, _) as eff) =
    let v, k, body = arm ctx env ty e ~resume:deep_resume ~discontinue:true eff in
    p
      "| %s %s -> Some (fun (%s : (a, %s) Effect.Deep.continuation) -> %s)"
      c
      v
      k
      (show_ty ty)
      body
  in
  p
    "(Effect.Deep.match_with (fun () -> %s) () { Effect.Deep.retc = (fun (%s : %s) -> \
     %s); exnc = %s; effc = (fun (type a) (eff : a Effect.t) -> match eff with %s | _ \
     -> None) })"
    (let c, a, r = List.nth handled (int_in ctx 0 (List.length handled - 1)) in
     if draw_silent ctx.tc (booleans ())
     then (
       let y = fresh ctx "y" in
       p
         "(let %s : %s = Effect.perform (%s %s) in %s)"
         y
         (show_ty r)
         c
         (e body_env a)
         (e (bind body_env y r) b))
     else e body_env b)
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
  let exnc =
    if catch then p "(function Exit -> %s | ex -> raise ex)" (e env ty) else "raise"
  in
  let arm ((c, _, _) as eff) =
    let resume k v _ = p "%s %s %s" go k v in
    let v, k, body = arm ctx env ty e ~resume ~discontinue:false eff in
    p
      "| %s %s -> Some (fun (%s : (a, %s) Effect.Shallow.continuation) -> %s)"
      c
      v
      k
      (show_ty b)
      body
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
    p "| effect %s %s, %s -> %s" c v k body
  in
  p
    "(match %s with | %s -> %s %s%s)"
    (e body_env b)
    x
    (e (bind env x b) ty)
    (String.concat " " (List.map arm handled))
    (if catch then p " | exception Exit -> %s" (e env ty) else "")
;;
