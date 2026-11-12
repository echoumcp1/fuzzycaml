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
         let hash = ox_syntax "#" "" in
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
           let this_constructor = ox_syntax "This" "Some" in
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
        (* Erased, the mutable is a ref. *)
        let read = ox_syntax var ("!" ^ var) in
        let loop_env =
          { (bind env loop_var Int) with mutables = (read, ty) :: env.mutables }
        in
        let step = expr loop_env ty in
        let count = expr env Int in
        let init = expr env ty in
        ox_syntax
          [%string
            "(let mutable %{var} : %{ty#Ty} = %{init} in for %{loop_var} = 0 to \
             (%{count} land 7) do %{var} <- %{step} done; %{var})"]
          [%string
            "(let %{var} = ref (%{init} : %{ty#Ty}) in for %{loop_var} = 0 to (%{count} \
             land 7) do %{var} := %{step} done; !%{var})"])
    ]
  else []
;;

(* A field of a declared record, or a field of an unboxed record that one holds,
   for a block index to point to. *)
type path =
  { decl : int
  ; fields : string list
  ; leaf_ty : ty
  ; is_mutable : bool
  }

(* Block indices do not support records stored as float arrays, nor float
   arrays. An unboxed record of one float is stored as the float. *)
let float_like ctx t = leaves ctx t = [ Float ]

let float_record ctx fields =
  List.for_all
    (fun (field : record_field) -> float_like ctx field.ty || field.ty = unboxed_float)
    fields
;;

let paths ctx =
  List.concat_map
    (fun (decl, decl_def) ->
       match decl_def with
       | Record fields when not (float_record ctx fields) ->
         List.concat_map
           (fun (field : record_field) ->
              let direct =
                { decl
                ; fields = [ field.name ]
                ; leaf_ty = field.ty
                ; is_mutable = field.is_mutable
                }
              in
              direct
              ::
              (match field.ty with
               | Named inner when !unboxed_record_decls.(inner) ->
                 (match ctx.decls.(inner) with
                  | URecord inner_fields ->
                    List.map
                      (fun (name, leaf_ty) ->
                         { direct with fields = [ field.name; name ]; leaf_ty })
                      inner_fields
                  | Record _ | Variant _ -> [])
               | _ -> []))
           fields
       | Record _ | URecord _ | Variant _ -> [])
    (indexed_decls ctx)
;;

(* Block indices into arrays of products do not yet support a value after a
   non-value. *)
let rec value_after_non_value = function
  | [] -> false
  | t :: rest ->
    (restricted t && List.exists (fun t -> not (restricted t)) rest)
    || value_after_non_value rest
;;

let indexable_elem ctx ty =
  (not (float_like ctx ty))
  && (not (value_after_non_value (leaves ctx ty)))
  && array_elem ctx ty
;;

let index path = "(." ^ String.concat ".#" path.fields ^ ")"
let access path = "." ^ String.concat "." path.fields

(* Erased, an unboxed record is a boxed one with immutable fields, so a write to
   one of its fields replaces it. *)
let erased_write record path value =
  match path.fields with
  | [ field; inner ] ->
    [%string "%{record}.%{field} <- { %{record}.%{field} with %{inner} = %{value} }"]
  | _ -> [%string "%{record}%{access path} <- %{value}"]
;;

(* Reads and writes through block indices, which erased are field and element
   accesses. *)
let indices ctx env ty gen =
  let expr = gen.expr in
  let reads =
    List.filter_map
      (fun path ->
         if path.leaf_ty <> ty
         then None
         else
           Some
             (fun () ->
               let record = fresh ctx "r" in
               let record_expr = expr env (Named path.decl) in
               let module_ = if path.is_mutable then "Idx_mut" else "Idx_imm" in
               ox_syntax
                 [%string
                   "(let %{record} = %{record_expr} in Stdlib_stable.%{module_}.get \
                    %{record} %{index path})"]
                 [%string "(%{record_expr})%{access path}"]))
      (paths ctx)
  in
  let writes =
    List.filter_map
      (fun path ->
         if path.leaf_ty <> ty || not path.is_mutable
         then None
         else
           Some
             (fun () ->
               let record = fresh ctx "r" in
               let value = fresh ctx "v" in
               let record_expr = fresh_record ctx env gen path.decl in
               let value_expr = expr env ty in
               let write =
                 ox_syntax
                   [%string "Stdlib_stable.Idx_mut.set %{record} %{index path} %{value}"]
                   (erased_write record path value)
               in
               let read =
                 ox_syntax
                   [%string "Stdlib_stable.Idx_mut.get %{record} %{index path}"]
                   [%string "%{record}%{access path}"]
               in
               [%string
                 "(let %{record} = %{record_expr} in let %{value} : %{ty#Ty} = \
                  %{value_expr} in %{write}; %{read})"]))
      (paths ctx)
  in
  let elements =
    if not (indexable_elem ctx ty)
    then []
    else
      [ (fun () ->
          let array = fresh ctx "a" in
          let array_expr = expr env (Arr ty) in
          let position =
            [%string "((%{expr env Int} land max_int) mod array_length %{array})"]
          in
          ox_syntax
            [%string
              "(let %{array} = %{array_expr} in Stdlib_stable.Idx_mut.get %{array} \
               (Stdlib_stable.Idx_mut.unsafe_create_into_array %{position}))"]
            [%string "(let %{array} = %{array_expr} in array_get %{array} %{position})"])
      ]
  in
  reads @ writes @ elements
;;

(* An address points into a block, so a collection that moves the block must
   update it. Erased, it is a field or element access. *)
let addresses ctx env ty gen =
  let expr = gen.expr in
  let through ~is_mutable ~write ~address ~erased_write ~erased_read =
    let pointer = fresh ctx "p" in
    let x = fresh ctx "x" in
    let value = fresh ctx "v" in
    let collection = pick ctx [ ""; "Gc.minor (); "; "Gc.compact (); " ] in
    let value_expr = if write then expr env ty else "" in
    let pattern = if is_mutable then "addr_" else "addr_imm_" in
    let bind_value = [%string "let %{value} : %{ty#Ty} = %{value_expr} in "] in
    let ox_write =
      if write
      then [%string "%{bind_value}Stdlib_stable.Addr.set %{pointer} %{value}; "]
      else ""
    in
    let erased_write =
      if write then [%string "%{bind_value}%{erased_write value}; "] else ""
    in
    ox_syntax
      [%string
        "(let %{pointer} = %{address} in %{collection}%{ox_write}match %{pointer} with \
         %{pattern} (%{x} : %{ty#Ty}) -> %{x})"]
      [%string "(%{collection}%{erased_write}%{erased_read})"]
  in
  let fields =
    List.filter_map
      (fun path ->
         if path.leaf_ty <> ty
         then None
         else
           Some
             (fun () ->
               let record = fresh ctx "r" in
               let write = path.is_mutable && flip ctx in
               let record_expr =
                 if write
                 then fresh_record ctx env gen path.decl
                 else expr env (Named path.decl)
               in
               let module_ = if path.is_mutable then "Addr" else "Addr_imm" in
               let body =
                 through
                   ~is_mutable:path.is_mutable
                   ~write
                   ~address:
                     [%string "Stdlib_stable.%{module_}.of_idx %{record} %{index path}"]
                   ~erased_write:(erased_write record path)
                   ~erased_read:[%string "%{record}%{access path}"]
               in
               [%string "(let %{record} = %{record_expr} in %{body})"]))
      (paths ctx)
  in
  let elements =
    if not (indexable_elem ctx ty)
    then []
    else
      [ (fun () ->
          let array = fresh ctx "a" in
          let position = fresh ctx "i" in
          let write = flip ctx in
          let array_expr =
            if write
            then
              [%string
                "(array_make (1 + (%{expr env Int} land 7)) (%{expr env ty} : %{ty#Ty}))"]
            else expr env (Arr ty)
          in
          let position_expr = expr env Int in
          let body =
            through
              ~is_mutable:true
              ~write
              ~address:
                [%string
                  "Stdlib_stable.Addr.of_idx %{array} \
                   (Stdlib_stable.Idx_mut.unsafe_create_into_array %{position})"]
              ~erased_write:(fun value ->
                [%string "array_set %{array} %{position} %{value}"])
              ~erased_read:[%string "array_get %{array} %{position}"]
          in
          [%string
            "(let %{array} = %{array_expr} in let %{position} = (%{position_expr} land \
             max_int) mod array_length %{array} in %{body})"])
      ]
  in
  fields @ elements
;;

let forms ctx env ty gen =
  if !ox_mode
  then
    boost (unboxed_and_mutable ctx env ty gen)
    @ (if on "indices" then indices ctx env ty gen else [])
    @ if on "addresses" then addresses ctx env ty gen else []
  else []
;;
