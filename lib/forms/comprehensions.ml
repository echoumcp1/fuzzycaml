open Config
open Ty
open Ctx
open Gen_ty
open Env

(* Comprehensions over ranges and lists or arrays, with their bounds and sources
   bound first. *)
let comprehensions ctx env ty gen =
  let expr = gen.expr in
  let value elem_ty = not (restricted elem_ty) in
  let clause iter =
    let var = fresh ctx "x" in
    match iter with
    | Some container when flip ctx ->
      let elem_ty = pick ctx (scanned ()) in
      let source = fresh ctx "src" in
      ( [%string "let %{source} = %{expr env (container elem_ty)} in "]
      , [%string "for %{var} in %{source}"]
      , var
      , elem_ty )
    | _ ->
      let low = fresh ctx "lo" in
      let high = fresh ctx "hi" in
      let bounds =
        [%string
          "let %{low} = (%{expr env Int} land 15) - 4 in let %{high} = (%{expr env Int} \
           land 15) - 4 in "]
      in
      if flip ctx
      then bounds, [%string "for %{var} = %{low} to %{high}"], var, Int
      else bounds, [%string "for %{var} = %{high} downto %{low}"], var, Int
  in
  (* The bindings before it and its clauses. *)
  let build iter elem_ty =
    let clauses = List.init (int_in ctx 1 2) (fun _ -> clause iter) in
    let body_env =
      List.fold_left
        (fun env (_, _, var, elem_ty) -> bind env var elem_ty)
        { (closure env) with handled_effects = [] }
        clauses
    in
    let body = expr body_env elem_ty in
    let condition = if flip ctx then Some (expr body_env Bool) else None in
    let ox =
      [%string "(%{body}) "]
      ^ String.concat " " (List.map (fun (_, clause, _, _) -> clause) clauses)
      ^ Option.fold
          ~none:""
          ~some:(fun condition_code -> [%string " when (%{condition_code})"])
          condition
    in
    String.concat "" (List.map (fun (lets, _, _, _) -> lets) clauses), ox
  in
  (match ty with
   | List elem_ty when value elem_ty ->
     [ (fun () ->
         let lets, ox = build (Some (fun elem_ty -> List elem_ty)) elem_ty in
         [%string "(%{lets}[ %{ox} ])"])
     ]
   | Arr elem_ty when value elem_ty ->
     [ (fun () ->
         let lets, ox = build (Some (fun elem_ty -> Arr elem_ty)) elem_ty in
         let elems = [%string "[| %{ox} |]"] in
         (* Readers of arrays assume they are not empty. *)
         [%string "(%{lets}Array.append %{elems} [| %{expr env elem_ty} |])"])
     ]
   | _ -> [])
  @ (if value ty
     then
       [ (fun () ->
           let lets, ox = build None ty in
           let default = fresh ctx "d" in
           let array = fresh ctx "ia" in
           let elems = [%string "[: %{ox} :]"] in
           [%string
             "(%{lets}let %{default} = %{expr env ty} in let %{array} = %{elems} in \
              Iarray.fold_left (fun (_ : %{ty#Ty}) (y : %{ty#Ty}) -> y) %{default} \
              %{array})"])
       ; (fun () ->
           let array = fresh ctx "ia" in
           let elems =
             String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> expr env ty))
           in
           [%string
             "(let %{array} = [: %{elems} :] in Iarray.get %{array} ((%{expr env Int} \
              land max_int) mod Iarray.length %{array}))"])
       ]
     else [])
  @
  if ty = Int
  then
    [ (fun () ->
        let lets, ox = build None Int in
        [%string "(%{lets}Iarray.length [: %{ox} :])"])
    ]
  else []
;;

let forms ctx env ty gen =
  boost (if !ox_mode && on "comprehensions" then comprehensions ctx env ty gen else [])
;;
