open Config
open Ty
open Ctx
open Literal
open Env
open Effects
open Ox
open Specific
open Generic

let rec expr ctx env ty depth =
  span
    ~name:("fuzzycaml.expr " ^ show_ty ty)
    ~ty
    ctx
    (fun () ->
       let e env t = expr ctx env t (depth - 1) in
       let vars = List.filter (fun (_, t) -> t = ty) (env.vars @ env.muts) in
       let unused = unused ctx vars in
       let use (x, _) =
         Hashtbl.replace ctx.used x ();
         x
       in
       let leaf () =
         (* i = 0 is the literal, so shrinking turns variable uses into constants. *)
         let i = int_in ctx 0 (List.length vars) in
         let prefer_unused = flip ~p:0.7 ctx in
         if unused <> [] && prefer_unused
         then use (pick ctx unused)
         else if i > 0
         then use (List.nth vars (i - 1))
         else (
           let l = literal ctx ty in
           (* Sys.opaque_identity keeps the compiler from folding the value away. *)
           if (not (restricted ty)) && on "opaque" && flip ~p:0.15 ctx
           then [%string "(Sys.opaque_identity %{l})"]
           else l)
       in
       let performs = List.filter (fun (_, _, r) -> r = ty) env.effs in
       (* Drawn whatever the depth and the variables in scope, so moving a
          subexpression or deleting a binding does not shift later choices.
          A leaf is false, which the shrinker tries first. *)
       let leaf_unused = not (flip ~p:0.5 ctx) in
       let leaf_var = not (flip ~p:0.75 ctx) in
       let use_other = flip ~p:0.3 ctx in
       if env.in_try && flip ~p:0.15 ctx
       then raise_at ctx ty
       else if depth <= 0 || (unused <> [] && leaf_unused) || (vars <> [] && leaf_var)
       then leaf ()
       else if performs <> [] && flip ~p:0.2 ctx
       then (
         let c, a, _ = pick ctx performs in
         [%string "(Effect.perform (%{c} %{e env a}))"])
       else if env.effs <> [] && flip ~p:0.35 ctx
       then perform_let ctx env e (pick ctx env.effs) ty
       else (
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
         | (x, t) :: _ when use_other ->
           [%string
             "(if %{use (x, t)} = %{literal ctx t} then %{e env ty} else %{e env ty})"]
         | _ ->
           if !ox_mode && immediate ty && on "locals" && flip ~p:0.15 ctx
           then local_binding ctx env ty e
           else if flip ~p:p_specific ctx
           then choose ctx (specific ctx env ty e)
           else choose ctx (leaf :: generic ctx env ty e)))
;;
