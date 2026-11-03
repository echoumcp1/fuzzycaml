open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Env
open Effects
open Ox
open Specific
open Generic

let rec body ctx env ty depth =
  let g = gen ctx (depth - 1) in
  let e = g.e in
  let vars = List.filter (fun (_, t) -> t = ty) (env.vars @ env.muts) in
  let unused = unused ctx vars in
  let use (x, _) =
    Hashtbl.replace ctx.used x ();
    x
  in
  let leaf () =
    let i = int_in ctx 0 (List.length vars) in
    let prefer_unused = flip ~p:(if unused = [] then 0. else 0.7) ctx in
    if i > 0 || prefer_unused
    then (
      let j =
        if prefer_unused then int_in ctx 0 (List.length unused - 1) else int_in ctx 0 0
      in
      use (if prefer_unused then List.nth unused j else List.nth vars (i - 1)))
    else (
      let l = literal ctx ty in
      if (not (restricted ty)) && on "opaque" && flip ~p:0.15 ctx
      then [%string "(Sys.opaque_identity %{l})"]
      else l)
  in
  let p_branch =
    if depth <= 0
    then 0.
    else if unused <> []
    then 0.375
    else if vars <> []
    then 0.75
    else 0.999
  in
  let is_leaf = not (flip ~p:p_branch ctx) in
  let other =
    List.filter
      (fun (x, t) -> t <> ty && first_order t && not (Hashtbl.mem ctx.used x))
      env.vars
  in
  let use_other = flip ~p:(if other = [] then 0. else 0.3) ctx in
  let performs = List.filter (fun (_, _, result) -> result = ty) env.effs in
  let raises = flip ~p:(if env.in_try then 0.15 else 0.) ctx in
  let performs_one = flip ~p:(if performs = [] then 0. else 0.2) ctx in
  let performs_let = flip ~p:(if env.effs = [] then 0. else 0.35) ctx in
  if raises
  then raise_at ctx ty
  else if is_leaf
  then leaf ()
  else if performs_one
  then (
    let con, arg, _ = pick ctx performs in
    [%string "(Effect.perform (%{con} %{e env arg}))"])
  else if performs_let
  then perform_let ctx env e (pick ctx env.effs) ty
  else (
    let p_specific =
      match ty with
      | Int | Bool | Float | Char | Int64 | Str | List _ | Num _ | U _ | Arr _ -> 0.7
      | Option _ | Pair _ | Arrow _ | Named _ | UTuple _ | Or_null _ -> 0.4
    in
    match other with
    | (x, t) :: _ when use_other ->
      [%string "(if %{use (x, t)} = %{literal ctx t} then %{e env ty} else %{e env ty})"]
    | _ ->
      if !ox_mode && immediate ty && on "locals" && flip ~p:0.15 ctx
      then local_binding ctx env ty g
      else if flip ~p:p_specific ctx
      then choose ctx (specific ctx env ty g)
      else choose ctx (leaf :: generic ctx env ty g))

and at ctx env ?candidates ?p ?(local = false) ?alt shape depth =
  span ~label:expr_label ctx (fun () ->
    let ty = draw_ty ctx ?candidates ?p shape in
    let locals = if local then List.filter (fun (_, t) -> t = ty) env.locals else [] in
    if locals <> []
    then ty, fst (pick ctx locals), true
    else (
      match Option.bind alt (fun alt -> alt ty) with
      | Some f -> ty, f (), false
      | None -> ty, body ctx env ty depth, false))

and gen ctx depth =
  { e =
      (fun env ty ->
        let _, s, _ = at ctx env (Is ty) depth in
        s)
  ; free =
      (fun ?candidates ?p env shape ->
        let ty, s, _ = at ctx env ?candidates ?p shape depth in
        ty, s)
  ; scrutinee =
      (fun ?candidates ?alt env shape ->
        let local = flip ~p:0.6 ctx in
        at ctx env ?candidates ~local ?alt shape depth)
  }
;;
