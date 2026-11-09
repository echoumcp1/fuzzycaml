open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Env
open Specific
open Generic

(* An expression of type [ty], at most [depth] levels deep. *)
let rec body ctx env ty depth =
  let gen = gen ctx (depth - 1) in
  let expr = gen.expr in
  let vars = List.filter (fun (_, var_ty) -> var_ty = ty) (env.vars @ env.mutables) in
  let unused = unused ctx vars in
  let use (var, _) =
    Hashtbl.replace ctx.used var ();
    var
  in
  let leaf () =
    let choice = int_in ctx 0 (List.length vars) in
    let prefer_unused = flip ~p:(if unused = [] then 0. else 0.7) ctx in
    if choice > 0 || prefer_unused
    then (
      let index =
        if prefer_unused then int_in ctx 0 (List.length unused - 1) else int_in ctx 0 0
      in
      use (if prefer_unused then List.nth unused index else List.nth vars (choice - 1)))
    else (
      let lit = literal ctx ty in
      if (not (restricted ty)) && on "opaque" && flip ~p:0.15 ctx
      then [%string "(Sys.opaque_identity %{lit})"]
      else lit)
  in
  let p_inner_node =
    if depth <= 0
    then 0.
    else if unused <> []
    then 0.375
    else if vars <> []
    then 0.75
    else 0.999
  in
  let is_leaf = not (flip ~p:p_inner_node ctx) in
  let other_vars =
    List.filter
      (fun (var, var_ty) ->
         var_ty <> ty && first_order var_ty && not (Hashtbl.mem ctx.used var))
      env.vars
  in
  let use_other = flip ~p:(if other_vars = [] then 0. else 0.3) ctx in
  let performs = List.filter (fun effect_ -> effect_.result = ty) env.handled_effects in
  let raises =
    flip ~p:(if env.in_try then 0.15 else if env.escapes then 0.04 else 0.) ctx
  in
  let performs_one = flip ~p:(if performs = [] then 0. else 0.2) ctx in
  let performs_let = flip ~p:(if env.handled_effects = [] then 0. else 0.35) ctx in
  if raises
  then raise_at ctx ty
  else if is_leaf
  then leaf ()
  else if performs_one
  then (
    let { constructor; arg; _ } = pick ctx performs in
    [%string "(Effect.perform (%{constructor} %{expr env arg}))"])
  else if performs_let
  then Effects.perform_let ctx env expr (pick ctx env.handled_effects) ty
  else (
    let p_specific =
      match ty with
      | Int | Bool | Float | Char | Int64 | Str | List _ | Num _ | Unboxed _ | Arr _ ->
        0.7
      | Option _ | Pair _ | Arrow _ | Named _ | UTuple _ | Or_null _ -> 0.4
    in
    match other_vars with
    | (var, var_ty) :: _ when use_other ->
      (* A comparison with a literal is almost always false, so the result rarely
         depends on [x]; a bit of its printed form is either about half the time. *)
      let condition =
        if !checks_on && (is_num var_ty || not (restricted var_ty)) && flip ~p:0.75 ctx
        then
          [%string
            "Hashtbl.hash (%{Printer.printer var_ty} %{use (var, var_ty)}) land 1 = 0"]
        else [%string "%{use (var, var_ty)} = %{literal ctx var_ty}"]
      in
      [%string "(if %{condition} then %{expr env ty} else %{expr env ty})"]
    | _ ->
      if !ox_mode && immediate ty && on "locals" && flip ~p:0.15 ctx
      then Locals.local_binding ctx env ty gen
      else if flip ~p:p_specific ctx
      then choose ctx (specific ctx env ty gen)
      else choose ctx (leaf :: generic ctx env ty gen))

(* An expression of a type drawn from [shape]: a local of that type when [local]
   allows it, else [alt]'s expression when it has one, else a new one. The
   result says whether the expression is a local. *)
and at ctx env ?candidates ?p ?(local = false) ?alt shape depth =
  span ~label:expr_label ctx (fun () ->
    let ty = draw_ty ctx ?candidates ?p shape in
    let locals = if local then List.filter (fun (_, t) -> t = ty) env.locals else [] in
    if locals <> []
    then ty, fst (pick ctx locals), true
    else (
      match Option.bind alt (fun alt -> alt ty) with
      | Some build -> ty, build (), false
      | None ->
        let code = body ctx env ty depth in
        (* A value the program would drop still reaches the output through [observe].
           Like [ticks], additions commute and only happen where order cannot matter. *)
        let code =
          if
            on "observe"
            && first_order ty
            && (not (restricted ty))
            && (not (handles_exit env))
            && (not env.in_fun)
            && env.handled_effects = []
            && !checks_on
            && flip ~p:0.1 ctx
          then (
            let observed = fresh ctx "o" in
            [%string
              "(let %{observed} = %{code} in observe (%{Printer.printer ty} \
               %{observed}); %{observed})"])
          else code
        in
        let code =
          if !props && !checks_on && flip ~p:0.1 ctx
          then (
            let key = fresh ctx "emi" in
            let replacement =
              without_checks (fun () -> (gen ctx (depth - 1)).expr env ty)
            in
            let prunable = flip ctx in
            if not !erase
            then Emi.regions := { Emi.key; replacement; prunable } :: !Emi.regions;
            Markers.region key code)
          else code
        in
        if !props && !checks_on && flip ~p:0.1 ctx
        then ty, Wrappers.neutral ctx env ty (gen ctx (depth - 1)) code, false
        else ty, code, false))

and gen ctx depth =
  { expr =
      (fun env ty ->
        let _, code, _ = at ctx env (Is ty) depth in
        code)
  ; of_shape =
      (fun ?candidates ?p env shape ->
        let ty, code, _ = at ctx env ?candidates ?p shape depth in
        ty, code)
  ; scrutinee =
      (fun ?candidates ?alt env shape ->
        let local = flip ~p:0.6 ctx in
        at ctx env ?candidates ~local ?alt shape depth)
  }
;;
