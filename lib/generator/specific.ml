open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Env

let binary env gen op operand_ty () =
  [%string "(%{gen.expr env operand_ty} %{op} %{gen.expr env operand_ty})"]
;;

(* Two values of the same first-order type, for comparisons. *)
let same_first_order ctx env gen =
  let operand_ty, first =
    gen.of_shape
      ~candidates:(candidates ctx env first_order_ty)
      env
      (Any first_order_types)
  in
  first, gen.expr env operand_ty
;;

let any_list ctx env gen =
  gen.of_shape ~candidates:(candidates ctx env lists) env (List_of (Any value_types))
;;

let call env gen fn arg_tys () =
  [%string {|(%{fn} %{String.concat " " (List.map (gen.expr env) arg_tys)})|}]
;;

let int_forms ctx env gen =
  let expr = gen.expr in
  List.map (fun op -> binary env gen op Int) [ "+"; "-"; "*"; "land"; "lor"; "lxor" ]
  @ List.map (fun f -> call env gen f [ Int ]) [ "abs"; "succ"; "pred"; "lnot"; "(~-)" ]
  @ List.map (fun f -> call env gen f [ Int; Int ]) [ "min"; "max"; "sdiv"; "smod" ]
  @ [ (fun () -> [%string "(%{expr env Int} / %{nonzero ctx})"])
    ; (fun () -> [%string "(%{expr env Int} mod %{nonzero ctx})"])
    ; (fun () ->
        let op = pick ctx [ "/"; "mod" ] in
        [%string "(try %{expr env Int} %{op} 0 with Division_by_zero -> %{expr env Int})"])
    ; (fun () ->
        let op = pick ctx [ "lsl"; "lsr"; "asr" ] in
        let amount =
          if flip ctx
          then [%string "(%{expr env Int} land 31)"]
          else string_of_int (int_in ctx 0 62)
        in
        [%string "(%{expr env Int} %{op} %{amount})"])
    ; (fun () ->
        let _, list = any_list ctx env gen in
        [%string "(List.length %{list})"])
    ; (fun () ->
        let first, second = same_first_order ctx env gen in
        [%string "(sgn (compare %{first} %{second}))"])
    ; call env gen "Bool.to_int" [ Bool ]
    ; call env gen "String.length" [ Str ]
    ; call env gen "Hashtbl.hash" [ Str ]
    ; (fun () -> [%string "(sgn (String.compare %{expr env Str} %{expr env Str}))"])
    ; (fun () -> Strings.string_load ctx env Int expr)
    ; call env gen "Char.code" [ Char ]
    ; call env gen "Int64.to_int" [ Int64 ]
    ; (fun () -> [%string "(sgn (Int64.compare %{expr env Int64} %{expr env Int64}))"])
    ; (fun () ->
        [%string "(sgn (Int64.unsigned_compare %{expr env Int64} %{expr env Int64}))"])
    ]
  @ (if has "popcount"
     then
       List.map
         (fun f -> call env gen f [ Int ])
         [ "Int.popcount"; "Int.leading_zeros"; "Int.trailing_zeros" ]
     else [])
  @ (if !ox_mode && on "numbers" then [ Numbers.converted env Int gen ] else [])
  @
  if on "arrays"
  then
    [ (fun () ->
        let _, first = gen.of_shape env (Arr_of 1) in
        [%string "(array_length %{first})"])
    ]
  else []
;;

let bool_forms ctx env gen =
  let expr = gen.expr in
  [ call env gen "not" [ Bool ]
  ; binary env gen "&&" Bool
  ; binary env gen "||" Bool
  ; call env gen "Float.is_integer" [ Float ]
  ; call env gen "String.equal" [ Str; Str ]
  ; call env gen "String.contains" [ Str; Char ]
  ; (fun () -> [%string "(String.starts_with ~prefix:%{expr env Str} %{expr env Str})"])
  ]
  @ (if !ox_mode && on "numbers"
     then [ (fun () -> Numbers.num_compare ctx env gen) ]
     else [])
  @ List.map
      (fun op () ->
         let first, second = same_first_order ctx env gen in
         [%string "(%{first} %{op} %{second})"])
      [ "="; "<>"; "<"; "<="; ">"; ">=" ]
  @ [ (fun () ->
        let lists =
          candidates ctx env (function
            | List elem_ty as t when first_order elem_ty -> Some t
            | _ -> None)
        in
        let list_ty, list =
          gen.of_shape ~candidates:lists env (List_of (Any first_order_types))
        in
        [%string "(List.mem %{expr env (elem_of list_ty)} %{list})"])
    ; (fun () ->
        let list_ty, list = any_list ctx env gen in
        let elem_ty = elem_of list_ty in
        let var = fresh ctx "x" in
        [%string
          "(List.exists (fun (%{var} : %{elem_ty#Ty}) -> %{expr (bind (closure env) var \
           elem_ty) Bool}) %{list})"])
    ]
;;

let float_forms env gen =
  let expr = gen.expr in
  List.map (fun op -> binary env gen op Float) [ "+."; "-."; "/." ]
  (* Opaque so arm64 cannot fuse the product into an fmadd, which rounds
       differently from ocamlc. *)
  @ [ (fun () ->
        [%string "(Sys.opaque_identity (%{expr env Float} *. %{expr env Float}))"])
    ]
  @ List.map
      (fun f -> call env gen f [ Float ])
      [ "sqrt"; "abs_float"; "floor"; "ceil"; "Float.trunc"; "Float.round"; "(~-.)" ]
  @ List.map
      (fun f -> call env gen f [ Float; Float ])
      [ "Float.min"; "Float.max"; "Float.rem"; "Float.min_num"; "Float.max_num" ]
  @ [ call env gen "Float.of_int" [ Int ]
    ; call env gen "Float.fma" [ Float; Float; Float ]
    ]
  @ (if !ox_mode then [ call env gen "box_float" [ unboxed_float ] ] else [])
  @ if !ox_mode && on "numbers" then [ Numbers.converted env Float gen ] else []
;;

let char_forms ctx env gen =
  let expr = gen.expr in
  [ (fun () -> [%string "(Char.chr (%{expr env Int} land 255))"])
  ; call env gen "Char.lowercase_ascii" [ Char ]
  ; call env gen "Char.uppercase_ascii" [ Char ]
  ; (fun () -> [%string "(Char.unsafe_chr (Char.code %{expr env Char}))"])
  ; (fun () -> Strings.string_load ctx env Char expr)
  ]
;;

let int64_forms ctx env gen =
  let expr = gen.expr in
  List.map
    (fun f -> call env gen f [ Int64; Int64 ])
    [ "Int64.add"
    ; "Int64.sub"
    ; "Int64.mul"
    ; "Int64.logand"
    ; "Int64.logor"
    ; "Int64.logxor"
    ; "i64div"
    ; "i64rem"
    ; "Int64.min"
    ; "Int64.max"
    ]
  @ List.map
      (fun f -> call env gen f [ Int64 ])
      [ "Int64.neg"; "Int64.abs"; "Int64.succ"; "Int64.pred"; "Int64.lognot" ]
  @ [ call env gen "Int64.of_int" [ Int ]
    ; (fun () -> Strings.string_load ctx env Int64 expr)
    ; (fun () -> [%string "(Int64.div %{expr env Int64} %{show_int64 (nonzero64 ctx)})"])
    ; (fun () -> [%string "(Int64.rem %{expr env Int64} %{show_int64 (nonzero64 ctx)})"])
    ; (fun () ->
        let op = pick ctx [ "Int64.unsigned_div"; "Int64.unsigned_rem" ] in
        [%string "(%{op} %{expr env Int64} %{show_int64 (nonzero64 ctx)})"])
    ; (fun () ->
        let op =
          pick
            ctx
            [ "Int64.shift_left"; "Int64.shift_right"; "Int64.shift_right_logical" ]
        in
        [%string "(%{op} %{expr env Int64} (%{expr env Int} land 63))"])
    ]
  @ if !ox_mode && on "numbers" then [ Numbers.converted env Int64 gen ] else []
;;

let string_forms ctx env gen =
  let expr = gen.expr in
  [ binary env gen "^" Str
  ; call env gen "ssub" [ Str; Int; Int ]
  ; call env gen "string_of_int" [ Int ]
  ; call env gen "Int64.to_string" [ Int64 ]
  ; call env gen "String.uppercase_ascii" [ Str ]
  ; call env gen "String.escaped" [ Str ]
  ; call env gen "String.trim" [ Str ]
  ; call env gen "(String.make 1)" [ Char ]
  ; (fun () -> [%string "(String.make (%{expr env Int} land 7) %{expr env Char})"])
  ; (fun () -> [%string "(String.concat %{expr env Str} %{expr env (List Str)})"])
  ; (fun () ->
      let loop_var = fresh ctx "i" in
      let char_expr = expr (bind (closure env) loop_var Int) Char in
      [%string
        "(String.init (%{expr env Int} land 7) (fun (%{loop_var} : int) -> %{char_expr}))"])
  ; (fun () ->
      let char_var = fresh ctx "c" in
      let string_var = expr env Str in
      let char_expr = expr (bind (closure env) char_var Char) Char in
      [%string "(String.map (fun (%{char_var} : char) -> %{char_expr}) %{string_var})"])
  ; (fun () ->
      let buffer = fresh ctx "b" in
      let loop_var = fresh ctx "i" in
      let loop_env = bind env loop_var Int in
      let char_expr = expr loop_env Char in
      let position = expr loop_env Int in
      [%string
        "(let %{buffer} = Bytes.of_string %{expr env Str} in for %{loop_var} = 0 to \
         (%{expr env Int} land 7) do if Bytes.length %{buffer} > 0 then Bytes.unsafe_set \
         %{buffer} ((%{position} land max_int) mod Bytes.length %{buffer}) %{char_expr} \
         done; Bytes.to_string %{buffer})"])
  ; (fun () ->
      let buffer = fresh ctx "b" in
      let loop_var = fresh ctx "i" in
      let loop_env = bind env loop_var Int in
      let char_expr = expr loop_env Char in
      let str_expr = expr loop_env Str in
      let count_expr = expr env Int in
      [%string
        "(let %{buffer} = Buffer.create (%{expr env Int} land 15) in for %{loop_var} = 0 \
         to (%{count_expr} land 7) do Buffer.add_string %{buffer} %{str_expr}; \
         Buffer.add_char %{buffer} %{char_expr} done; Buffer.contents %{buffer})"])
  ; (fun () ->
      let string_var = fresh ctx "s" in
      let buffer = fresh ctx "b" in
      (* The padding fits any store at the first [String.length] + 1 offsets; past
         them a store may be out of bounds, and must not write any byte. *)
      let past_end = flip ctx in
      let offsets = if past_end then "16" else "1" in
      let offset =
        [%string
          "((%{expr env Int} land max_int) mod (String.length %{string_var} + \
           %{offsets}))"]
      in
      let store =
        choose
          ctx
          [ (fun () -> [%string "Bytes.set_uint8 %{buffer} %{offset} %{expr env Int}"])
          ; (fun () -> [%string "Bytes.set_int16_le %{buffer} %{offset} %{expr env Int}"])
          ; (fun () ->
              [%string "Bytes.set_uint16_be %{buffer} %{offset} %{expr env Int}"])
          ; (fun () ->
              [%string
                "Bytes.set_int32_le %{buffer} %{offset} (Int32.of_int %{expr env Int})"])
          ; (fun () ->
              [%string
                "Bytes.set_int32_be %{buffer} %{offset} (Int32.of_int %{expr env Int})"])
          ; (fun () ->
              [%string "Bytes.set_int64_le %{buffer} %{offset} %{expr env Int64}"])
          ; (fun () ->
              [%string "Bytes.set_int64_be %{buffer} %{offset} %{expr env Int64}"])
          ]
      in
      let store =
        if past_end
        then [%string "(try %{store} with Invalid_argument _ -> ())"]
        else store
      in
      [%string
        "(let %{string_var} = %{expr env Str} in let %{buffer} = Bytes.of_string \
         (%{string_var} ^ \"\\001\\002\\003\\004\\005\\006\\007\\008\") in %{store}; \
         Bytes.to_string %{buffer})"])
  ]
;;

let unboxed_float_forms ctx env ty gen =
  List.map
    (fun f -> call env gen f [ unboxed_float; unboxed_float ])
    [ "fu_add"; "fu_sub"; "fu_mul"; "fu_div" ]
  @ [ call env gen "fu_sqrt" [ unboxed_float ]; call env gen "unbox_float" [ Float ] ]
  @ if on "numbers" then Numbers.num_ops ctx env ty gen else []
;;

let array_forms ctx env ty gen elem_ty =
  let expr = gen.expr in
  let length () = [%string "(1 + (%{expr env Int} land 7))"] in
  (* An unboxed product array needs its element layout, which [raise Exit] doesn't fix. *)
  let elem () = [%string "(%{expr env elem_ty} : %{elem_ty#Ty})"] in
  [ (fun () ->
      let elems = String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> elem ())) in
      [%string "[| %{elems} |]"])
  ; (fun () -> [%string "(array_make %{length ()} %{elem ()})"])
  ; (fun () ->
      (* Each index comes from the loop, so it is in bounds. *)
      let array_var = fresh ctx "a" in
      let loop_var = fresh ctx "i" in
      let loop_env =
        bind
          (bind env loop_var Int)
          [%string "(array_get %{array_var} %{loop_var})"]
          elem_ty
      in
      [%string
        "(let %{array_var} = array_make %{length ()} %{elem ()} in for %{loop_var} = 0 \
         to array_length %{array_var} - 1 do array_set %{array_var} %{loop_var} %{expr \
         loop_env elem_ty} done; %{array_var})"])
  ; (fun () ->
      (* The index may be past the end. *)
      let array_var = fresh ctx "a" in
      [%string
        "(let %{array_var} = array_make %{length ()} %{elem ()} in (try array_set \
         %{array_var} (%{expr env Int} land 15) %{expr env elem_ty} with \
         Invalid_argument _ -> ()); %{array_var})"])
  ]
  @ (match elem_ty with
     | Arr inner_ty ->
       [ (fun () ->
           let loop_var = fresh ctx "i" in
           let elem_expr = expr (bind (closure env) loop_var Int) elem_ty in
           [%string "(Array.init %{length ()} (fun (%{loop_var} : int) -> %{elem_expr}))"])
       ; (fun () ->
           let array_var = fresh ctx "a" in
           let row = fresh ctx "r" in
           let loop_var = fresh ctx "i" in
           let inner_var = fresh ctx "j" in
           let loop_env =
             bind
               (bind (bind env loop_var Int) inner_var Int)
               [%string "(array_get %{row} %{inner_var})"]
               inner_ty
           in
           let cell_expr = expr loop_env inner_ty in
           let init_expr = expr (closure env) inner_ty in
           [%string
             "(let %{array_var} = Array.init %{length ()} (fun _ -> array_make %{length \
              ()} %{init_expr}) in for %{loop_var} = 0 to array_length %{array_var} - 1 \
              do let %{row} = array_get %{array_var} %{loop_var} in for %{inner_var} = 0 \
              to array_length %{row} - 1 do array_set %{row} %{inner_var} %{cell_expr} \
              done done; %{array_var})"])
       ]
     | _ -> [])
  (* The compiler picks how to store an array from its element type, so these
       hide that type behind a GADT, a polymorphic function or a call. *)
  @
  match elem_ty with
  | Unboxed _ | UTuple _ -> []
  | _ ->
    let witness () =
      pick
        ctx
        ("AwAny"
         ::
         (match elem_ty with
          | Float -> [ "AwFloat" ]
          | Int -> [ "AwInt" ]
          | _ -> []))
    in
    [ (fun () -> [%string "(arr_of %{witness ()} %{length ()} %{expr env elem_ty})"])
    ; (fun () -> [%string "(arr_poly %{length ()} %{expr env elem_ty})"])
    ; (fun () -> [%string "(arr_copy %{expr env ty})"])
    ; (fun () ->
        let make = fresh ctx "mk" in
        [%string
          "(let %{make} (type a) (x : a) (y : a) : a array = [| x; y; x |] in %{make} \
           %{expr env elem_ty} %{expr env elem_ty})"])
    ]
;;

let list_forms ctx env ty gen elem_ty =
  let expr = gen.expr in
  [ (fun () -> [%string "(%{expr env elem_ty} :: %{expr env ty})"])
  ; (fun () -> [%string "[%{expr env elem_ty}; %{expr env elem_ty}]"])
  ; call env gen "List.rev" [ ty ]
  ; binary env gen "@" ty
  ; (fun () ->
      let list_ty, list = any_list ctx env gen in
      let source_ty = elem_of list_ty in
      let var = fresh ctx "x" in
      let body = expr (bind (closure env) var source_ty) elem_ty in
      [%string "(List.map (fun (%{var} : %{source_ty#Ty}) -> %{body}) %{list})"])
  ; (fun () ->
      let var = fresh ctx "x" in
      let list = expr env ty in
      let keep_expr = expr (bind (closure env) var elem_ty) Bool in
      [%string "(List.filter (fun (%{var} : %{elem_ty#Ty}) -> %{keep_expr}) %{list})"])
  ; (fun () ->
      let index = fresh ctx "i" in
      let elem_expr = expr (bind (closure env) index Int) elem_ty in
      [%string
        "(List.init (%{expr env Int} land 7) (fun (%{index} : int) -> %{elem_expr}))"])
  ]
  @ (if first_order elem_ty
     then [ (fun () -> [%string "(List.sort compare %{expr env ty})"]) ]
     else [])
  @ boost (if on "tmc" then [ (fun () -> Tmc.tmc ctx env elem_ty expr) ] else [])
;;

let option_forms ctx env gen content_ty =
  let expr = gen.expr in
  [ (fun () -> [%string "(Some %{expr env content_ty})"])
  ; (fun () ->
      let var = fresh ctx "x" in
      [%string
        "(List.find_opt (fun (%{var} : %{content_ty#Ty}) -> %{expr (bind (closure env) \
         var content_ty) Bool}) %{expr env (List content_ty)})"])
  ; (fun () ->
      let options =
        candidates ctx env (function
          | Option _ as content_ty -> Some content_ty
          | _ -> None)
      in
      let option_ty, option =
        gen.of_shape ~candidates:options env (Option_of (Any value_types))
      in
      let source_ty =
        match option_ty with
        | Option source_ty -> source_ty
        | _ -> assert false
      in
      let var = fresh ctx "x" in
      let body = expr (bind (closure env) var source_ty) content_ty in
      [%string "(Option.map (fun (%{var} : %{source_ty#Ty}) -> %{body}) %{option})"])
  ]
;;

let named_forms ctx env ty gen decl =
  let expr = gen.expr in
  match ctx.decls.(decl) with
  | URecord fields ->
    let field_values_expr () = field_values (expr env) fields in
    [ (fun () -> urecord (field_values_expr ()))
    ; (fun () ->
        let field, field_ty = pick ctx fields in
        urecord [%string "%{expr env ty} with %{field} = %{expr env field_ty}"])
    ]
    @ List.filter_map
        (fun (boxed, unboxed) ->
           if unboxed <> decl
           then None
           else
             Some
               (fun () ->
                 let source = fresh ctx "s" in
                 let copy_field (field, _) =
                   [%string
                     "%{field} = %{source}.%{String.sub field 1 (String.length field - \
                      1)}"]
                 in
                 let fields = String.concat "; " (List.map copy_field fields) in
                 let boxed = expr env (Named boxed) in
                 [%string "(let %{source} = %{boxed} in %{urecord fields})"]))
        !unboxed_twins
  | Variant constrs ->
    List.map (fun (c, args) () -> construct c (List.map (expr env) args)) constrs
    @ List.concat_map
        (fun (child, parent) ->
           if child = decl
           then (
             let up () =
               [%string "(%{expr env (Named parent)} : t%{parent#Int} :> t%{child#Int})"]
             in
             [ up; up; up ])
           else [])
        !extended_variants
  | Record fields ->
    let field_values_expr () = field_values (expr env) (field_types fields) in
    [ (fun () -> [%string "{ %{field_values_expr ()} }"])
    ; (fun () ->
        let field = pick ctx fields in
        [%string "{ %{expr env ty} with %{field.name} = %{expr env field.ty} }"])
    ]
    @ List.filter_map
        (fun (boxed, unboxed) ->
           if boxed <> decl
           then None
           else
             Some
               (fun () ->
                 let source = fresh ctx "s" in
                 let dot = ox_syntax ".#" "." in
                 let copy_field field =
                   [%string "%{field.name} = %{source}%{dot}u%{field.name}"]
                 in
                 let fields = String.concat "; " (List.map copy_field fields) in
                 [%string
                   "(let %{source} = %{expr env (Named unboxed)} in { %{fields} })"]))
        !unboxed_twins
    @
    (* Only a record the expression allocates is mutated, and only before it
          is returned. *)
    (match List.filter (fun field -> field.is_mutable) fields with
      | [] -> []
      | mutables ->
        [ (fun () ->
            let record = fresh ctx "r" in
            let loop_var = fresh ctx "i" in
            let field = pick ctx mutables in
            let loop_env =
              List.fold_left
                (fun env other -> bind env [%string "%{record}.%{other.name}"] other.ty)
                (bind env loop_var Int)
                fields
            in
            [%string
              "(let %{record} = { %{field_values_expr ()} } in for %{loop_var} = 0 to \
               (%{expr env Int} land 7) do %{record}.%{field.name} <- %{expr loop_env \
               field.ty} done; %{record})"])
        ])
;;

let specific ctx env ty gen =
  let expr = gen.expr in
  match ty with
  | Int -> int_forms ctx env gen
  | Bool -> bool_forms ctx env gen
  | Float -> float_forms env gen
  | Char -> char_forms ctx env gen
  | Int64 -> int64_forms ctx env gen
  | Str -> string_forms ctx env gen
  | Unboxed UFloat -> unboxed_float_forms ctx env ty gen
  | Num _ | Unboxed _ -> Numbers.num_ops ctx env ty gen
  | UTuple ts -> [ (fun () -> utuple (List.map (expr env) ts)) ]
  | Or_null t -> [ (fun () -> null ()); (fun () -> this (expr env t)) ]
  | Arr t -> array_forms ctx env ty gen t
  | List t -> list_forms ctx env ty gen t
  | Option t -> option_forms ctx env gen t
  | Pair (a, b) -> [ (fun () -> [%string "(%{expr env a}, %{expr env b})"]) ]
  | Arrow (a, b) ->
    [ (fun () ->
        let x = fresh ctx "x" in
        [%string "(fun (%{x} : %{a#Ty}) -> %{expr (bind (escape env) x a) b})"])
    ]
  | Named i -> named_forms ctx env ty gen i
;;
