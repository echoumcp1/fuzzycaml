open Hegel
open Config
open Ty
open Ctx
open Literal
open Env
open Ox
open Specific
open Generic

let rec expr ctx env ty depth =
  span ctx (fun () ->
    let vars = List.filter (fun (_, t) -> t = ty) (env.vars @ env.muts) in
    let unused = List.filter (fun (x, _) -> not (Hashtbl.mem ctx.used x)) vars in
    let use (x, _) =
      Hashtbl.replace ctx.used x ();
      x
    in
    let leaf () =
      (* i = 0 is the literal, so shrinking turns variable uses into constants. *)
      let i = int_in ctx 0 (List.length vars) in
      if unused <> [] && draw_silent ctx.tc (booleans ~p:0.7 ())
      then use (List.nth unused (int_in ctx 0 (List.length unused - 1)))
      else if i > 0
      then use (List.nth vars (i - 1))
      else (
        let l = literal ctx ty in
        (* Sys.opaque_identity keeps the compiler from folding the value away. *)
        if (not (restricted ty)) && on "opaque" && draw_silent ctx.tc (booleans ~p:0.15 ())
        then p "(Sys.opaque_identity %s)" l
        else l)
    in
    let performs = List.filter (fun (_, _, r) -> r = ty) env.effs in
    if env.in_try && draw_silent ctx.tc (booleans ~p:0.15 ())
    then raise_at ctx ty
    else if
      depth <= 0
      || (unused <> [] && draw_silent ctx.tc (booleans ~p:0.5 ()))
      || (vars <> [] && draw_silent ctx.tc (booleans ~p:0.25 ()))
    then leaf ()
    else if performs <> [] && draw_silent ctx.tc (booleans ~p:0.2 ())
    then (
      let c, a, _ = List.nth performs (int_in ctx 0 (List.length performs - 1)) in
      p "(Effect.perform (%s %s))" c (expr ctx env a (depth - 1)))
    else if env.effs <> [] && draw_silent ctx.tc (booleans ~p:0.35 ())
    then (
      let c, a, r = List.nth env.effs (int_in ctx 0 (List.length env.effs - 1)) in
      let x = fresh ctx "y" in
      p
        "(let %s : %s = Effect.perform (%s %s) in %s)"
        x
        (show_ty r)
        c
        (expr ctx env a (depth - 1))
        (expr ctx (bind env x r) ty (depth - 1)))
    else (
      let e env t = expr ctx env t (depth - 1) in
      let other =
        List.filter
          (fun (x, t) -> t <> ty && first_order t && not (Hashtbl.mem ctx.used x))
          env.vars
      in
      (* Prefer operations on [ty] over structural forms, so values are computed
         and not only passed around. *)
      let p_specific =
        match ty with
        | Int | Bool | Float | Char | Int64 | Str | List _ | Num _ | U _ | Arr _ -> 0.7
        | Option _ | Pair _ | Arrow _ | Named _ | UTuple _ | Or_null _ -> 0.4
      in
      match other with
      | (x, t) :: _ when draw_silent ctx.tc (booleans ~p:0.3 ()) ->
        (* use the newest unused variable of another type *)
        p "(if %s = %s then %s else %s)" (use (x, t)) (literal ctx t) (e env ty) (e env ty)
      | _ ->
      if !ox_mode && immediate ty && on "locals" && draw_silent ctx.tc (booleans ~p:0.15 ())
      then local_binding ctx env ty e
      else if draw_silent ctx.tc (booleans ~p:p_specific ())
      then choose ctx (specific ctx env ty e)
      else choose ctx (leaf :: generic ctx env ty e)))
;;
