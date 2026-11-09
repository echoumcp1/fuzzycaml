open Config
open Ty
open Ctx
open Env
open Gen_ty

let handler_setup ctx env =
  let handled = subset ctx 3 ctx.effects in
  let handled = if handled = [] then [ List.hd ctx.effects ] else handled in
  let catches_exit = flip ~p:0.3 ctx in
  ( handled
  , catches_exit
  , { env with
      handled_effects = handled @ env.handled_effects
    ; in_try = env.in_try || catches_exit
    } )
;;

let computation ctx env handled gen =
  let results = List.map (fun effect_ -> effect_.result) handled in
  gen.of_shape
    ~candidates:(results @ candidates ctx env first_order_ty)
    ~p:0.95
    env
    (Any first_order_types)
;;

type arm =
  { payload : string
  ; continuation : string
  ; body : string
  }

let arm_body ctx env ty expr ~resume ~discontinue { arg; result; _ } =
  let payload = fresh ctx "v" in
  let continuation = fresh ctx "k" in
  let arm_env = bind env payload arg in
  let resumed_result = fresh ctx "r" in
  let resumed () = resume continuation (expr arm_env result) result in
  { payload
  ; continuation
  ; body =
      choose
        ctx
        ([ resumed
         ; (fun () ->
             [%string
               "(let %{resumed_result} : %{ty#Ty} = %{resumed ()} in %{expr (bind \
                arm_env resumed_result ty) ty})"])
         ; (fun () -> [%string "(ignore %{continuation}; %{expr arm_env ty})"])
         ]
         @
         if discontinue && env.in_try
         then [ (fun () -> [%string "Effect.Deep.discontinue %{continuation} Exit"]) ]
         else [])
  }
;;

let deep_resume continuation value result =
  [%string "Effect.Deep.continue %{continuation} (%{value} : %{result#Ty})"]
;;

let exception_handler env ty expr catches_exit =
  if catches_exit
  then [%string "(function Exit -> %{expr env ty} | ex -> raise ex)"]
  else "raise"
;;

let perform_let ctx env expr { constructor; arg; result } ty =
  let performed = fresh ctx "y" in
  let body = expr (bind env performed result) ty in
  [%string
    "(let %{performed} : %{result#Ty} = Effect.perform (%{constructor} %{expr env arg}) \
     in %{body})"]
;;

(* The computation, arms and [retc] are closures. *)
let without_captures env = { env with locals = []; mutables = [] }

let handler ctx env ty gen =
  let env = without_captures env in
  let expr = gen.expr in
  let handled, catches_exit, body_env = handler_setup ctx env in
  let returned = fresh ctx "x" in
  let exnc = exception_handler env ty expr catches_exit in
  let arm ({ constructor; _ } as effect_) =
    let { payload; continuation; body } =
      arm_body ctx env ty expr ~resume:deep_resume ~discontinue:true effect_
    in
    [%string
      "| %{constructor} %{payload} -> Some (fun (%{continuation} : (a, %{ty#Ty}) \
       Effect.Deep.continuation) -> %{body})"]
  in
  let arms = String.concat " " (List.map arm handled) in
  let body_ty, body =
    let { constructor; arg; result } = pick ctx handled in
    if flip ctx
    then (
      let performed = fresh ctx "y" in
      let body_ty, inner = computation ctx (bind body_env performed result) handled gen in
      ( body_ty
      , [%string
          "(let %{performed} : %{result#Ty} = Effect.perform (%{constructor} %{expr \
           body_env arg}) in %{inner})"] ))
    else computation ctx body_env handled gen
  in
  let ret = expr (bind env returned body_ty) ty in
  [%string
    "(Effect.Deep.match_with (fun () -> %{body}) () { Effect.Deep.retc = (fun \
     (%{returned} : %{body_ty#Ty}) -> %{ret}); exnc = %{exnc}; effc = (fun (type a) (eff \
     : a Effect.t) -> match eff with %{arms} | _ -> None) })"]
;;

let shallow ctx env ty gen =
  let env = without_captures env in
  let expr = gen.expr in
  let handled, catches_exit, body_env = handler_setup ctx env in
  let continue_ = fresh ctx "go" in
  let type_var = fresh ctx "c" in
  let returned = fresh ctx "x" in
  let exnc = exception_handler env ty expr catches_exit in
  let body_ty, body = computation ctx body_env handled gen in
  let arm ({ constructor; _ } as effect_) =
    let resume continuation value _ = [%string "%{continue_} %{continuation} %{value}"] in
    let { payload; continuation; body } =
      arm_body ctx env ty expr ~resume ~discontinue:false effect_
    in
    [%string
      "| %{constructor} %{payload} -> Some (fun (%{continuation} : (a, %{body_ty#Ty}) \
       Effect.Shallow.continuation) -> %{body})"]
  in
  let arms = String.concat " " (List.map arm handled) in
  let ret = expr (bind env returned body_ty) ty in
  [%string
    "(let rec %{continue_} : type %{type_var}. (%{type_var}, %{body_ty#Ty}) \
     Effect.Shallow.continuation -> %{type_var} -> %{ty#Ty} = fun k v -> \
     Effect.Shallow.continue_with k v { Effect.Shallow.retc = (fun (%{returned} : \
     %{body_ty#Ty}) -> %{ret}); exnc = %{exnc}; effc = (fun (type a) (eff : a Effect.t) \
     -> match eff with %{arms} | _ -> None) } in %{continue_} (Effect.Shallow.fiber (fun \
     () -> %{body})) ())"]
;;

let effect_match ctx env ty gen =
  let expr = gen.expr in
  let handled, catches_exit, body_env = handler_setup ctx env in
  let returned = fresh ctx "x" in
  let body_ty, body = computation ctx body_env handled gen in
  let arm ({ constructor; _ } as effect_) =
    let { payload; continuation; body } =
      arm_body ctx env ty expr ~resume:deep_resume ~discontinue:true effect_
    in
    [%string "| effect %{constructor} %{payload}, %{continuation} -> %{body}"]
  in
  let exit_arm =
    if catches_exit then [%string " | exception Exit -> %{expr env ty}"] else ""
  in
  let arms = String.concat " " (List.map arm handled) in
  let ret = expr (bind env returned body_ty) ty in
  [%string "(match %{body} with | %{returned} -> %{ret} %{arms}%{exit_arm})"]
;;

let forms ctx env ty gen =
  let available = first_order ty && ctx.effects <> [] in
  boost (if available && on "deep" then [ (fun () -> handler ctx env ty gen) ] else [])
  @ boost
      (if available && on "shallow" then [ (fun () -> shallow ctx env ty gen) ] else [])
  @ boost
      (if available && !effect_syntax_on && on "effect_syntax"
       then [ (fun () -> effect_match ctx env ty gen) ]
       else [])
;;
