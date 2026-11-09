open Config
open Ty
open Ctx
open Gen_ty
open Env

(* Comprehensions over ranges and lists or arrays, with their bounds and sources
   bound first so that every version evaluates them once and in the same order. The
   erased version builds the same elements with List. *)
let comprehensions ctx env ty gen =
  let expr = gen.expr in
  let erasing = !Config.erase in
  let value elem_ty = not (restricted elem_ty) in
  let clause iter =
    let var = fresh ctx "x" in
    match iter with
    | Some (container, to_list) when flip ctx ->
      let elem_ty = pick ctx (scanned ()) in
      let source = fresh ctx "src" in
      ( [%string "let %{source} = %{expr env (container elem_ty)} in "]
      , [%string "for %{var} in %{source}"]
      , to_list source
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
      let count = [%string "(max 0 (%{high} - %{low} + 1))"] in
      if flip ctx
      then
        ( bounds
        , [%string "for %{var} = %{low} to %{high}"]
        , [%string "(List.init %{count} (fun k -> %{low} + k))"]
        , var
        , Int )
      else
        ( bounds
        , [%string "for %{var} = %{high} downto %{low}"]
        , [%string "(List.init %{count} (fun k -> %{high} - k))"]
        , var
        , Int )
  in
  (* The bindings before it, its clauses for OxCaml, and the erased list. *)
  let build iter elem_ty =
    let clauses = List.init (int_in ctx 1 2) (fun _ -> clause iter) in
    let body_env =
      List.fold_left
        (fun env (_, _, _, var, elem_ty) -> bind env var elem_ty)
        { (closure env) with handled_effects = [] }
        clauses
    in
    let body = expr body_env elem_ty in
    let condition = if flip ctx then Some (expr body_env Bool) else None in
    let rec erased = function
      | [ (_, _, source, var, elem_ty) ] ->
        (match condition with
         | Some condition_code ->
           [%string
             "(List.filter_map (fun (%{var} : %{elem_ty#Ty}) -> if %{condition_code} \
              then Some (%{body}) else None) %{source})"]
         | None ->
           [%string "(List.map (fun (%{var} : %{elem_ty#Ty}) -> %{body}) %{source})"])
      | (_, _, source, var, elem_ty) :: rest ->
        [%string
          "(List.concat_map (fun (%{var} : %{elem_ty#Ty}) -> %{erased rest}) %{source})"]
      | [] -> assert false
    in
    let ox =
      [%string "(%{body}) "]
      ^ String.concat " " (List.map (fun (_, clause, _, _, _) -> clause) clauses)
      ^ Option.fold
          ~none:""
          ~some:(fun condition_code -> [%string " when (%{condition_code})"])
          condition
    in
    ( String.concat "" (List.map (fun (lets, _, _, _, _) -> lets) clauses)
    , ox
    , erased clauses )
  in
  let iarray_module = Config.ox_syntax "Iarray" "Array" in
  (match ty with
   | List elem_ty when value elem_ty ->
     [ (fun () ->
         let lets, ox, erased =
           build (Some ((fun elem_ty -> List elem_ty), Fun.id)) elem_ty
         in
         if erasing
         then [%string "(%{lets}%{erased})"]
         else [%string "(%{lets}[ %{ox} ])"])
     ]
   | Arr elem_ty when value elem_ty ->
     [ (fun () ->
         let lets, ox, erased =
           build
             (Some
                ( (fun elem_ty -> Arr elem_ty)
                , fun array -> [%string "(Array.to_list %{array})"] ))
             elem_ty
         in
         let elems =
           if erasing
           then [%string "(Array.of_list %{erased})"]
           else [%string "[| %{ox} |]"]
         in
         (* Readers of arrays assume they are not empty. *)
         [%string "(%{lets}Array.append %{elems} [| %{expr env elem_ty} |])"])
     ]
   | _ -> [])
  @ (if value ty
     then
       [ (fun () ->
           let lets, ox, erased = build None ty in
           let default = fresh ctx "d" in
           let array = fresh ctx "ia" in
           let elems =
             if erasing
             then [%string "(Array.of_list %{erased})"]
             else [%string "[: %{ox} :]"]
           in
           [%string
             "(%{lets}let %{default} = %{expr env ty} in let %{array} = %{elems} in \
              %{iarray_module}.fold_left (fun (_ : %{ty#Ty}) (y : %{ty#Ty}) -> y) \
              %{default} %{array})"])
       ; (fun () ->
           let array = fresh ctx "ia" in
           let elems =
             String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> expr env ty))
           in
           let open_, close = if erasing then "[|", "|]" else "[:", ":]" in
           [%string
             "(let %{array} = %{open_} %{elems} %{close} in %{iarray_module}.get \
              %{array} ((%{expr env Int} land max_int) mod %{iarray_module}.length \
              %{array}))"])
       ]
     else [])
  @
  if ty = Int
  then
    [ (fun () ->
        let lets, ox, erased = build None Int in
        if erasing
        then [%string "(%{lets}List.length %{erased})"]
        else [%string "(%{lets}%{iarray_module}.length [: %{ox} :])"])
    ]
  else []
;;

let forms ctx env ty gen =
  boost (if !ox_mode && on "comprehensions" then comprehensions ctx env ty gen else [])
;;
