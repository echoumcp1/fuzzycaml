open Ctx
open Env

let handler_setup ctx env =
  let handled = List.filter (fun _ -> flip ctx) ctx.effects in
  let handled = if handled = [] then [ List.hd ctx.effects ] else handled in
  let b =
    from_env
      ctx
      { env with vars = List.map (fun (con, _, result) -> con, result) handled }
      some_ty
      (fun () -> fo_env_ty ctx env)
  in
  let catch = flip ~p:0.3 ctx in
  handled, b, catch, { env with effs = handled @ env.effs; in_try = env.in_try || catch }
;;

(* The bound value, continuation and body of a handler's arm for one effect. *)
let arm_body ctx env ty e ~resume ~discontinue (_, arg, result) =
  let v = fresh ctx "v" in
  let k = fresh ctx "k" in
  let henv = bind env v arg in
  let r = fresh ctx "r" in
  let resumed () = resume k (e henv result) result in
  ( v
  , k
  , choose
      ctx
      ([ resumed
       ; (fun () ->
           [%string "(let %{r} : %{ty#Ty} = %{resumed ()} in %{e (bind henv r ty) ty})"])
       ; (fun () -> [%string "(ignore %{k}; %{e henv ty})"])
       ]
       @
       if discontinue && env.in_try
       then [ (fun () -> [%string "Effect.Deep.discontinue %{k} Exit"]) ]
       else []) )
;;

let deep_resume k v result = [%string "Effect.Deep.continue %{k} (%{v} : %{result#Ty})"]

let exnc env ty e catch =
  if catch then [%string "(function Exit -> %{e env ty} | ex -> raise ex)"] else "raise"
;;

let perform_let ctx env e (con, arg, result) ty =
  let y = fresh ctx "y" in
  let body = e (bind env y result) ty in
  [%string "(let %{y} : %{result#Ty} = Effect.perform (%{con} %{e env arg}) in %{body})"]
;;

let handler ctx env ty e =
  let handled, b, catch, body_env = handler_setup ctx env in
  let x = fresh ctx "x" in
  let exnc = exnc env ty e catch in
  let arm ((con, _, _) as eff) =
    let v, k, body = arm_body ctx env ty e ~resume:deep_resume ~discontinue:true eff in
    [%string
      "| %{con} %{v} -> Some (fun (%{k} : (a, %{ty#Ty}) Effect.Deep.continuation) -> \
       %{body})"]
  in
  let arms = String.concat " " (List.map arm handled) in
  let ret = e (bind env x b) ty in
  let body =
    let eff = pick ctx handled in
    if flip ctx then perform_let ctx body_env e eff b else e body_env b
  in
  [%string
    "(Effect.Deep.match_with (fun () -> %{body}) () { Effect.Deep.retc = (fun (%{x} : \
     %{b#Ty}) -> %{ret}); exnc = %{exnc}; effc = (fun (type a) (eff : a Effect.t) -> \
     match eff with %{arms} | _ -> None) })"]
;;

let shallow ctx env ty e =
  let handled, b, catch, body_env = handler_setup ctx env in
  let go = fresh ctx "go" in
  let tv = fresh ctx "c" in
  let x = fresh ctx "x" in
  let exnc = exnc env ty e catch in
  let arm ((con, _, _) as eff) =
    let resume k v _ = [%string "%{go} %{k} %{v}"] in
    let v, k, body = arm_body ctx env ty e ~resume ~discontinue:false eff in
    [%string
      "| %{con} %{v} -> Some (fun (%{k} : (a, %{b#Ty}) Effect.Shallow.continuation) -> \
       %{body})"]
  in
  let body = e body_env b in
  let arms = String.concat " " (List.map arm handled) in
  let ret = e (bind env x b) ty in
  [%string
    "(let rec %{go} : type %{tv}. (%{tv}, %{b#Ty}) Effect.Shallow.continuation -> %{tv} \
     -> %{ty#Ty} = fun k v -> Effect.Shallow.continue_with k v { Effect.Shallow.retc = \
     (fun (%{x} : %{b#Ty}) -> %{ret}); exnc = %{exnc}; effc = (fun (type a) (eff : a \
     Effect.t) -> match eff with %{arms} | _ -> None) } in %{go} (Effect.Shallow.fiber \
     (fun () -> %{body})) ())"]
;;

let effect_match ctx env ty e =
  let handled, b, catch, body_env = handler_setup ctx env in
  let x = fresh ctx "x" in
  let arm ((con, _, _) as eff) =
    let v, k, body = arm_body ctx env ty e ~resume:deep_resume ~discontinue:true eff in
    [%string "| effect %{con} %{v}, %{k} -> %{body}"]
  in
  let exit_arm = if catch then [%string " | exception Exit -> %{e env ty}"] else "" in
  let arms = String.concat " " (List.map arm handled) in
  let ret = e (bind env x b) ty in
  [%string "(match %{e body_env b} with | %{x} -> %{ret} %{arms}%{exit_arm})"]
;;
