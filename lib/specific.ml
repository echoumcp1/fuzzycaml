open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Env
open Ox
open Stress
open Forms

let specific ctx env ty e =
  let bin op t () = [%string "(%{e env t} %{op} %{e env t})"] in
  let call f args () =
    [%string {|(%{f} %{String.concat " " (List.map (e env) args)})|}]
  in
  match ty with
  | Int ->
    List.map (fun op -> bin op Int) [ "+"; "-"; "*"; "land"; "lor"; "lxor" ]
    @ List.map (fun f -> call f [ Int ]) [ "abs"; "succ"; "pred"; "lnot"; "(~-)" ]
    @ List.map (fun f -> call f [ Int; Int ]) [ "min"; "max"; "sdiv"; "smod" ]
    @ [ (fun () -> [%string "(%{e env Int} / %{nonzero ctx})"])
      ; (fun () -> [%string "(%{e env Int} mod %{nonzero ctx})"])
      ; (fun () ->
          let op = pick ctx [ "/"; "mod" ] in
          [%string "(try %{e env Int} %{op} 0 with Division_by_zero -> %{e env Int})"])
      ; (fun () ->
          let op = pick ctx [ "lsl"; "lsr"; "asr" ] in
          let amount =
            if flip ctx
            then [%string "(%{e env Int} land 31)"]
            else string_of_int (int_in ctx 0 62)
          in
          [%string "(%{e env Int} %{op} %{amount})"])
      ; (fun () -> [%string "(List.length %{e env (List (env_ty ctx env elem))})"])
      ; (fun () ->
          let s = fo_env_ty ctx env in
          [%string "(sgn (compare %{e env s} %{e env s}))"])
      ; call "Bool.to_int" [ Bool ]
      ; call "String.length" [ Str ]
      ; call "Hashtbl.hash" [ Str ]
      ; (fun () -> [%string "(sgn (String.compare %{e env Str} %{e env Str}))"])
      ; (fun () -> str_load ctx env Int e)
      ; call "Char.code" [ Char ]
      ; call "Int64.to_int" [ Int64 ]
      ; (fun () -> [%string "(sgn (Int64.compare %{e env Int64} %{e env Int64}))"])
      ]
    @ (if !ox_mode && on "numbers" then [ converted ctx env Int e ] else [])
    @
    if on "arrays"
    then [ (fun () -> [%string "(array_length %{e env (Arr (array_elem ctx 1))})"]) ]
    else []
  | Bool ->
    [ call "not" [ Bool ]
    ; bin "&&" Bool
    ; bin "||" Bool
    ; call "Float.is_integer" [ Float ]
    ; call "String.equal" [ Str; Str ]
    ; call "String.contains" [ Str; Char ]
    ; (fun () -> [%string "(String.starts_with ~prefix:%{e env Str} %{e env Str})"])
    ]
    @ (if !ox_mode && on "numbers" then [ (fun () -> num_compare ctx env e) ] else [])
    @ List.map
        (fun op () ->
           let s = fo_env_ty ctx env in
           [%string "(%{e env s} %{op} %{e env s})"])
        [ "="; "<>"; "<"; "<="; ">"; ">=" ]
    @ [ (fun () ->
          let s = fo_env_ty ctx env in
          [%string "(List.mem %{e env s} %{e env (List s)})"])
      ; (fun () ->
          let s = env_ty ctx env elem in
          let x = fresh ctx "x" in
          [%string
            "(List.exists (fun (%{x} : %{s#Ty}) -> %{e (bind (closure env) x s) Bool}) \
             %{e env (List s)})"])
      ]
  | Float ->
    List.map (fun op -> bin op Float) [ "+."; "-."; "/." ]
    (* opaque so arm64 cannot fuse the product into an fmadd, which rounds differently
       from ocamlc *)
    @ [ (fun () -> [%string "(Sys.opaque_identity (%{e env Float} *. %{e env Float}))"]) ]
    @ List.map
        (fun f -> call f [ Float ])
        [ "sqrt"; "abs_float"; "floor"; "ceil"; "Float.trunc"; "Float.round"; "(~-.)" ]
    @ List.map
        (fun f -> call f [ Float; Float ])
        [ "Float.min"; "Float.max"; "Float.rem" ]
    @ [ call "Float.of_int" [ Int ]; call "Float.fma" [ Float; Float; Float ] ]
    @ (if !ox_mode then [ call "box_float" [ float_u ] ] else [])
    @ if !ox_mode && on "numbers" then [ converted ctx env Float e ] else []
  | Char ->
    [ (fun () -> [%string "(Char.chr (%{e env Int} land 255))"])
    ; call "Char.lowercase_ascii" [ Char ]
    ; call "Char.uppercase_ascii" [ Char ]
    ; (fun () -> [%string "(Char.unsafe_chr (Char.code %{e env Char}))"])
    ; (fun () -> str_load ctx env Char e)
    ]
  | Int64 ->
    List.map
      (fun f -> call f [ Int64; Int64 ])
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
        (fun f -> call f [ Int64 ])
        [ "Int64.neg"; "Int64.abs"; "Int64.succ"; "Int64.pred"; "Int64.lognot" ]
    @ [ call "Int64.of_int" [ Int ]
      ; (fun () -> str_load ctx env Int64 e)
      ; (fun () -> [%string "(Int64.div %{e env Int64} %{int64_lit (nonzero64 ctx)})"])
      ; (fun () -> [%string "(Int64.rem %{e env Int64} %{int64_lit (nonzero64 ctx)})"])
      ; (fun () ->
          let op =
            pick
              ctx
              [ "Int64.shift_left"; "Int64.shift_right"; "Int64.shift_right_logical" ]
          in
          [%string "(%{op} %{e env Int64} (%{e env Int} land 63))"])
      ]
    @ if !ox_mode && on "numbers" then [ converted ctx env Int64 e ] else []
  | Str ->
    [ bin "^" Str
    ; call "ssub" [ Str; Int; Int ]
    ; call "string_of_int" [ Int ]
    ; call "Int64.to_string" [ Int64 ]
    ; call "String.uppercase_ascii" [ Str ]
    ; call "String.escaped" [ Str ]
    ; call "String.trim" [ Str ]
    ; call "(String.make 1)" [ Char ]
    ; (fun () -> [%string "(String.make (%{e env Int} land 7) %{e env Char})"])
    ; (fun () -> [%string "(String.concat %{e env Str} %{e env (List Str)})"])
    ; (fun () ->
        let i = fresh ctx "i" in
        let char = e (bind (closure env) i Int) Char in
        [%string "(String.init (%{e env Int} land 7) (fun (%{i} : int) -> %{char}))"])
    ; (fun () ->
        let c = fresh ctx "c" in
        let s = e env Str in
        let char = e (bind (closure env) c Char) Char in
        [%string "(String.map (fun (%{c} : char) -> %{char}) %{s})"])
    ; (fun () ->
        let b = fresh ctx "b" in
        let i = fresh ctx "i" in
        let env' = bind env i Int in
        let char = e env' Char in
        let pos = e env' Int in
        [%string
          "(let %{b} = Bytes.of_string %{e env Str} in for %{i} = 0 to (%{e env Int} \
           land 7) do if Bytes.length %{b} > 0 then Bytes.unsafe_set %{b} ((%{pos} land \
           max_int) mod Bytes.length %{b}) %{char} done; Bytes.to_string %{b})"])
    ; (fun () ->
        let b = fresh ctx "b" in
        let i = fresh ctx "i" in
        let env' = bind env i Int in
        let char = e env' Char in
        let str = e env' Str in
        let count = e env Int in
        [%string
          "(let %{b} = Buffer.create (%{e env Int} land 15) in for %{i} = 0 to (%{count} \
           land 7) do Buffer.add_string %{b} %{str}; Buffer.add_char %{b} %{char} done; \
           Buffer.contents %{b})"])
    ; (fun () ->
        let s = fresh ctx "s" in
        let b = fresh ctx "b" in
        let off =
          [%string "((%{e env Int} land max_int) mod (String.length %{s} + 1))"]
        in
        let store =
          choose
            ctx
            [ (fun () -> [%string "Bytes.set_uint8 %{b} %{off} %{e env Int}"])
            ; (fun () -> [%string "Bytes.set_int16_le %{b} %{off} %{e env Int}"])
            ; (fun () -> [%string "Bytes.set_uint16_be %{b} %{off} %{e env Int}"])
            ; (fun () ->
                [%string "Bytes.set_int32_le %{b} %{off} (Int32.of_int %{e env Int})"])
            ; (fun () ->
                [%string "Bytes.set_int32_be %{b} %{off} (Int32.of_int %{e env Int})"])
            ; (fun () -> [%string "Bytes.set_int64_le %{b} %{off} %{e env Int64}"])
            ; (fun () -> [%string "Bytes.set_int64_be %{b} %{off} %{e env Int64}"])
            ]
        in
        [%string
          "(let %{s} = %{e env Str} in let %{b} = Bytes.of_string (%{s} ^ \
           \"\\001\\002\\003\\004\\005\\006\\007\\008\") in %{store}; Bytes.to_string \
           %{b})"])
    ]
  | U UF ->
    List.map
      (fun f -> call f [ float_u; float_u ])
      [ "fu_add"; "fu_sub"; "fu_mul"; "fu_div" ]
    @ [ call "fu_sqrt" [ float_u ]; call "unbox_float" [ Float ] ]
    @ if on "numbers" then num_ops ctx env ty e else []
  | Num _ | U _ -> num_ops ctx env ty e
  | UTuple ts ->
    [ (fun () -> [%string {|#(%{String.concat ", " (List.map (e env) ts)})|}]) ]
  | Or_null t -> [ (fun () -> "Null"); (fun () -> [%string "(This %{e env t})"]) ]
  | Arr t ->
    let n () = [%string "(1 + (%{e env Int} land 7))"] in
    [ (fun () ->
        let elems = String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> e env t)) in
        [%string "[| %{elems} |]"])
    ; (fun () -> [%string "(array_make %{n ()} %{e env t})"])
    ; (fun () ->
        (* each index comes from the loop, so it is in bounds *)
        let a = fresh ctx "a" in
        let i = fresh ctx "i" in
        let env' = bind (bind env i Int) [%string "(array_get %{a} %{i})"] t in
        [%string
          "(let %{a} = array_make %{n ()} %{e env t} in for %{i} = 0 to array_length \
           %{a} - 1 do array_set %{a} %{i} %{e env' t} done; %{a})"])
    ]
    @ (match t with
       | Arr s ->
         [ (fun () ->
             let i = fresh ctx "i" in
             let elem = e (bind (closure env) i Int) t in
             [%string "(Array.init %{n ()} (fun (%{i} : int) -> %{elem}))"])
         ; (fun () ->
             let a = fresh ctx "a" in
             let r = fresh ctx "r" in
             let i = fresh ctx "i" in
             let j = fresh ctx "j" in
             let env' =
               bind (bind (bind env i Int) j Int) [%string "(array_get %{r} %{j})"] s
             in
             let cell = e env' s in
             let init = e (closure env) s in
             [%string
               "(let %{a} = Array.init %{n ()} (fun _ -> array_make %{n ()} %{init}) in \
                for %{i} = 0 to array_length %{a} - 1 do let %{r} = array_get %{a} %{i} \
                in for %{j} = 0 to array_length %{r} - 1 do array_set %{r} %{j} %{cell} \
                done done; %{a})"])
         ]
       | _ -> [])
    (* The compiler picks how to store an array from its element type, so these
       hide that type behind a GADT, a polymorphic function or a call. *)
    @
      (match t with
      | U _ -> []
      | _ ->
        let w () =
          pick
            ctx
            ("AwAny"
             ::
             (match t with
              | Float -> [ "AwFloat" ]
              | Int -> [ "AwInt" ]
              | _ -> []))
        in
        [ (fun () -> [%string "(arr_of %{w ()} %{n ()} %{e env t})"])
        ; (fun () -> [%string "(arr_poly %{n ()} %{e env t})"])
        ; (fun () -> [%string "(arr_copy %{e env ty})"])
        ; (fun () ->
            let mk = fresh ctx "mk" in
            [%string
              "(let %{mk} (type a) (x : a) (y : a) : a array = [| x; y; x |] in %{mk} \
               %{e env t} %{e env t})"])
        ])
  | List t ->
    [ (fun () -> [%string "(%{e env t} :: %{e env ty})"])
    ; (fun () -> [%string "[%{e env t}; %{e env t}]"])
    ; call "List.rev" [ ty ]
    ; bin "@" ty
    ; (fun () ->
        let s = env_ty ctx env elem in
        let x = fresh ctx "x" in
        let l = e env (List s) in
        let body = e (bind (closure env) x s) t in
        [%string "(List.map (fun (%{x} : %{s#Ty}) -> %{body}) %{l})"])
    ; (fun () ->
        let x = fresh ctx "x" in
        let l = e env ty in
        let keep = e (bind (closure env) x t) Bool in
        [%string "(List.filter (fun (%{x} : %{t#Ty}) -> %{keep}) %{l})"])
    ; (fun () ->
        let i = fresh ctx "i" in
        let elem = e (bind (closure env) i Int) t in
        [%string "(List.init (%{e env Int} land 7) (fun (%{i} : int) -> %{elem}))"])
    ]
    @ (if first_order t
       then [ (fun () -> [%string "(List.sort compare %{e env ty})"]) ]
       else [])
    @ boost (if on "tmc" then [ (fun () -> tmc ctx env t e) ] else [])
  | Option t ->
    [ (fun () -> [%string "(Some %{e env t})"])
    ; (fun () ->
        let x = fresh ctx "x" in
        [%string
          "(List.find_opt (fun (%{x} : %{t#Ty}) -> %{e (bind (closure env) x t) Bool}) \
           %{e env (List t)})"])
    ; (fun () ->
        let s =
          env_ty ctx env (function
            | Option s -> Some s
            | _ -> None)
        in
        let x = fresh ctx "x" in
        let o = e env (Option s) in
        let body = e (bind (closure env) x s) t in
        [%string "(Option.map (fun (%{x} : %{s#Ty}) -> %{body}) %{o})"])
    ]
  | Pair (a, b) -> [ (fun () -> [%string "(%{e env a}, %{e env b})"]) ]
  | Arrow (a, b) ->
    [ (fun () ->
        let x = fresh ctx "x" in
        [%string "(fun (%{x} : %{a#Ty}) -> %{e (bind (escape env) x a) b})"])
    ]
  | Named i ->
    (match ctx.decls.(i) with
     | URecord fields ->
       let build () = field_values (e env) fields in
       [ (fun () -> [%string "#{ %{build ()} }"])
       ; (fun () ->
           let field, field_ty = pick ctx fields in
           [%string "#{ %{e env ty} with %{field} = %{e env field_ty} }"])
       ]
       @ List.filter_map
           (fun (boxed, unboxed) ->
              if unboxed <> i
              then None
              else
                Some
                  (fun () ->
                    let s = fresh ctx "s" in
                    let copy (field, _) =
                      [%string
                        "%{field} = %{s}.%{String.sub field 1 (String.length field - 1)}"]
                    in
                    let fields = String.concat "; " (List.map copy fields) in
                    [%string "(let %{s} = %{e env (Named boxed)} in #{ %{fields} })"]))
           !twins
     | Variant constrs ->
       List.map (fun (c, args) () -> construct c (List.map (e env) args)) constrs
       @ List.concat_map
           (fun (child, parent) ->
              if child = i
              then (
                let up () =
                  [%string "(%{e env (Named parent)} : t%{parent#Int} :> t%{child#Int})"]
                in
                [ up; up; up ])
              else [])
           !poly_parent
     | Record fields ->
       let build () = field_values (e env) (field_types fields) in
       [ (fun () -> [%string "{ %{build ()} }"])
       ; (fun () ->
           let field, field_ty, _ = pick ctx fields in
           [%string "{ %{e env ty} with %{field} = %{e env field_ty} }"])
       ]
       @ List.filter_map
           (fun (boxed, unboxed) ->
              if boxed <> i
              then None
              else
                Some
                  (fun () ->
                    let s = fresh ctx "s" in
                    let copy (field, _, _) = [%string "%{field} = %{s}.#u%{field}"] in
                    let fields = String.concat "; " (List.map copy fields) in
                    [%string "(let %{s} = %{e env (Named unboxed)} in { %{fields} })"]))
           !twins
       @
       (* Only a record the expression allocates is mutated, and only before it
          is returned. *)
       (match List.filter (fun (_, _, is_mutable) -> is_mutable) fields with
         | [] -> []
         | mutables ->
           [ (fun () ->
               let r = fresh ctx "r" in
               let i = fresh ctx "i" in
               let field, field_ty, _ = pick ctx mutables in
               let env' =
                 List.fold_left
                   (fun env (other, other_ty, _) ->
                      bind env [%string "%{r}.%{other}"] other_ty)
                   (bind env i Int)
                   fields
               in
               [%string
                 "(let %{r} = { %{build ()} } in for %{i} = 0 to (%{e env Int} land 7) \
                  do %{r}.%{field} <- %{e env' field_ty} done; %{r})"])
           ]))
;;
