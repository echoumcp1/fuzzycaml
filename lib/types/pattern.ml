open Config
open Ty
open Ctx
open Gen_ty
open Literal

let gen_decl ctx =
  if on "records" && flip ctx
  then (
    let all_float = flip ~p:0.3 ctx in
    let float_ty = if !ox_mode && flip ctx then unboxed_float else Float in
    let unboxed () =
      if on "numbers" then Unboxed (pick ctx unboxed_numbers) else unboxed_float
    in
    Record
      (repeat ctx 1 4 (fun _ ->
         let field = fresh ctx "f" in
         let field_ty =
           if all_float
           then float_ty
           else if !ox_mode && flip ~p:0.25 ctx
           then unboxed ()
           else first_order_type ctx
         in
         field, field_ty, flip ~p:0.3 ctx)))
  else (
    let poly = (not !ox_mode) && on "poly" && flip ~p:0.35 ctx in
    let own_constructors () =
      repeat ctx 1 4 (fun _ ->
        let constructor = fresh ctx (if poly then "`C" else "C") in
        let args = repeat ctx 0 3 (fun _ -> first_order_type ctx) in
        if (not poly) && args <> [] && flip ~p:0.3 ctx
        then inline_records := constructor :: !inline_records;
        constructor, args)
    in
    let poly_variants =
      List.filter_map
        (fun (parent, decl) ->
           match decl with
           | Variant ((constructor, _) :: _ as constructors) when constructor.[0] = '`' ->
             Some (parent, constructors)
           | _ -> None)
        (indexed_decls ctx)
    in
    if poly && poly_variants <> [] && flip ctx
    then (
      let parent, inherited = pick ctx poly_variants in
      extended_variants := (Array.length ctx.decls, parent) :: !extended_variants;
      Variant (inherited @ own_constructors ()))
    else Variant (own_constructors ()))
;;

let small_int ctx = paren (string_of_int (int_in ctx (-2) 5))

let pattern_int ctx =
  choose
    ctx
    [ (fun () -> "0")
    ; (fun () -> small_int ctx)
    ; (fun () -> small_int ctx)
    ; (fun () -> "1")
    ; (fun () -> "(-1)")
    ; (fun () -> paren (string_of_int (int_in ctx (-100) 100)))
    ; (fun () -> paren (string_of_int (1 lsl int_in ctx 0 61)))
    ; (fun () -> "4611686018427387903")
    ]
;;

(* A pattern for [ty] and the variables it binds. At the root of a match it is
   never only a variable. Both sides of an or-pattern must bind the same
   variables, so they are drawn with [~binds:false], which binds none. *)
let rec pattern ?(at_root = false) ctx ty depth ~binds =
  let without_vars pattern = pattern, [] in
  let var_pattern () =
    if binds
    then (
      let bound_var = fresh ctx "q" in
      bound_var, [ bound_var, ty ])
    else without_vars "_"
  in
  let smaller elem_ty = pattern ctx elem_ty (depth - 1) ~binds in
  let structural =
    match ty with
    | Int -> [ (fun () -> without_vars (pattern_int ctx)) ]
    | Bool -> [ (fun () -> without_vars "true"); (fun () -> without_vars "false") ]
    | Char ->
      [ (fun () -> without_vars (char_literal ctx))
      ; (fun () ->
          let first = int_in ctx 0 255 in
          let second = int_in ctx first (min 255 (first + int_in ctx 0 30)) in
          without_vars (Printf.sprintf "(%C .. %C)" (Char.chr first) (Char.chr second)))
      ; (fun () ->
          let first = int_in ctx (Char.code 'a') (Char.code 'h') in
          let second = int_in ctx first (Char.code 'h') in
          without_vars (Printf.sprintf "(%C .. %C)" (Char.chr first) (Char.chr second)))
      ]
    | Int64 ->
      [ (fun () ->
          without_vars
            (choose
               ctx
               [ (fun () -> show_int64 (Int64.of_int (int_in ctx (-2) 5)))
               ; (fun () -> "0L")
               ; (fun () -> "9223372036854775807L")
               ; (fun () -> show_int64 (Int64.shift_left 1L (int_in ctx 0 62)))
               ]))
      ]
    | Str -> [ (fun () -> without_vars (string_literal ctx)) ]
    | Float | Arrow _ | Num _ | Unboxed _ | UTuple _ | Or_null _ | Arr _ -> []
    | List elem_ty ->
      [ (fun () -> without_vars "[]")
      ; (fun () ->
          let head_pattern, head_vars = smaller elem_ty in
          let tail_pattern, tail_vars = smaller ty in
          [%string "(%{head_pattern} :: %{tail_pattern})"], head_vars @ tail_vars)
      ; (fun () ->
          let first, first_vars = smaller elem_ty in
          let second, second_vars = smaller elem_ty in
          [%string "[%{first}; %{second}]"], first_vars @ second_vars)
      ]
    | Option elem_ty ->
      [ (fun () -> without_vars "None")
      ; (fun () ->
          let first, first_vars = smaller elem_ty in
          [%string "(Some %{first})"], first_vars)
      ]
    | Pair (first, second) ->
      [ (fun () ->
          let first_pattern, first_vars = smaller first in
          let second_pattern, second_vars = smaller second in
          [%string "(%{first_pattern}, %{second_pattern})"], first_vars @ second_vars)
      ]
    | Named decl ->
      (match ctx.decls.(decl) with
       | Record fields ->
         [ (fun () ->
             let picked =
               match subset ctx 4 fields with
               | [] -> [ List.hd fields ]
               | picked -> picked
             in
             let parts =
               List.map (fun (field, field_ty, _) -> field, smaller field_ty) picked
             in
             ( Printf.sprintf
                 "{ %s_ }"
                 (String.concat
                    ""
                    (List.map
                       (fun (field, (pat, _)) -> [%string "%{field} = %{pat}; "])
                       parts))
             , List.concat_map (fun (_, (_, bound)) -> bound) parts ))
         ]
       | Variant constrs ->
         List.map
           (fun (constructor, args) () ->
              let parts = List.map smaller args in
              construct constructor (List.map fst parts), List.concat_map snd parts)
           constrs
       | URecord _ -> [])
  in
  let combined =
    if structural = []
    then []
    else
      [ (fun () ->
          let first, _ = pattern ctx ty (depth - 1) ~binds:false in
          let second, _ = pattern ctx ty (depth - 1) ~binds:false in
          without_vars [%string "(%{first} | %{second})"])
      ]
      @
      if binds
      then
        [ (fun () ->
            let inner, inner_vars = smaller ty in
            let bound_var = fresh ctx "q" in
            [%string "(%{inner} as %{bound_var})"], (bound_var, ty) :: inner_vars)
        ]
      else []
  in
  if depth > 0 && structural <> [] && (at_root || flip ~p:0.75 ctx)
  then choose ctx (structural @ combined)
  else choose ctx [ (fun () -> without_vars "_"); var_pattern ]
;;
