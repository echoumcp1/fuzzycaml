open Config
open Ty
open Ctx
open Gen_ty
open Env

let unboxed_and_mutable ctx env ty gen =
  let expr = gen.expr in
  (if on "utuples"
   then
     [ (fun () ->
         let utuples =
           candidates ctx env (function
             | UTuple component_tys as t when List.mem ty component_tys -> Some t
             | _ -> None)
         in
         let at_front = flip ctx in
         let shape =
           UTuple_of
             (if at_front then [ Is ty; Any all_types ] else [ Any all_types; Is ty ])
         in
         let utuple_ty, tuple = gen.of_shape ~candidates:utuples env shape in
         let component_tys =
           match utuple_ty with
           | UTuple component_tys -> component_tys
           | _ -> assert false
         in
         let components = List.map (fun t -> fresh ctx "u", t) component_tys in
         let names = String.concat ", " (List.map fst components) in
         let hash = "#" in
         [%string
           "(let %{hash}(%{names}) = %{tuple} in %{expr (bind_all env components) ty})"])
     ]
   else [])
  @ (if on "or_null"
     then
       [ (fun () ->
           let nulls =
             candidates ctx env (function
               | Or_null _ as t -> Some t
               | _ -> None)
           in
           let nullable_ty, nullable =
             gen.of_shape ~candidates:nulls env (Or_null_of (Any value_types))
           in
           let value_ty =
             match nullable_ty with
             | Or_null value_ty -> value_ty
             | _ -> assert false
           in
           let var = fresh ctx "x" in
           let this_branch = expr (bind env var value_ty) ty in
           let this_constructor = "This" in
           [%string
             "(match %{nullable} with %{Literal.null ()} -> %{expr env ty} | \
              %{this_constructor} %{var} -> %{this_branch})"])
       ]
     else [])
  @
  if
    on "mutables"
    &&
    match ty with
    | UTuple _ | Or_null _ -> false
    | Named decl -> not !unboxed_record_decls.(decl)
    | _ -> true
  then
    [ (fun () ->
        let var = fresh ctx "mu" in
        let loop_var = fresh ctx "i" in
        let loop_env =
          { (bind env loop_var Int) with mutables = (var, ty) :: env.mutables }
        in
        let step = expr loop_env ty in
        let count = expr env Int in
        let init = expr env ty in
        [%string
          "(let mutable %{var} : %{ty#Ty} = %{init} in for %{loop_var} = 0 to (%{count} \
           land 7) do %{var} <- %{step} done; %{var})"])
    ]
  else []
;;

let forms ctx env ty gen = if !ox_mode then unboxed_and_mutable ctx env ty gen else []
