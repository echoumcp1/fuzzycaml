open Hegel
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
  let bin op t = fun () -> p "(%s %s %s)" (e env t) op (e env t) in
  let call f args = fun () -> p "(%s %s)" f (String.concat " " (List.map (e env) args)) in
  match ty with
  | Int ->
    List.map (fun op -> bin op Int) [ "+"; "-"; "*"; "land"; "lor"; "lxor" ]
    @ List.map (fun f -> call f [ Int ]) [ "abs"; "succ"; "pred"; "lnot"; "(~-)" ]
    @ List.map (fun f -> call f [ Int; Int ]) [ "min"; "max"; "sdiv"; "smod" ]
    @ [ (fun () -> p "(%s / %s)" (e env Int) (nonzero ctx))
      ; (fun () -> p "(%s mod %s)" (e env Int) (nonzero ctx))
      ; (fun () ->
          let op = choose ctx (List.map (fun o () -> o) [ "/"; "mod" ]) in
          p "(try %s %s 0 with Division_by_zero -> %s)" (e env Int) op (e env Int))
      ; (fun () ->
          let op = choose ctx (List.map (fun o () -> o) [ "lsl"; "lsr"; "asr" ]) in
          let amount =
            if draw_silent ctx.tc (booleans ())
            then p "(%s land 31)" (e env Int)
            else string_of_int (int_in ctx 0 62)
          in
          p "(%s %s %s)" (e env Int) op amount)
      ; (fun () -> p "(List.length %s)" (e env (List (env_ty ctx env elem))))
      ; (fun () ->
          let s = fo_env_ty ctx env in
          p "(sgn (compare %s %s))" (e env s) (e env s))
      ; call "Bool.to_int" [ Bool ]
      ; call "String.length" [ Str ]
      ; call "Hashtbl.hash" [ Str ]
      ; (fun () -> p "(sgn (String.compare %s %s))" (e env Str) (e env Str))
      ; (fun () -> str_load ctx env e Int)
      ; call "Char.code" [ Char ]
      ; call "Int64.to_int" [ Int64 ]
      ; (fun () -> p "(sgn (Int64.compare %s %s))" (e env Int64) (e env Int64))
      ]
    @ (if !ox_mode && on "numbers" then [ List.hd (num_ops ctx env Int e) ] else [])
    @ (if !ox_mode && on "arrays"
       then [ (fun () -> p "(array_length %s)" (e env (Arr (array_elem ctx 1)))) ]
       else [])
  | Bool ->
    [ call "not" [ Bool ]
    ; bin "&&" Bool
    ; bin "||" Bool
    ; call "Float.is_integer" [ Float ]
    ; call "String.equal" [ Str; Str ]
    ; call "String.contains" [ Str; Char ]
    ; (fun () -> p "(String.starts_with ~prefix:%s %s)" (e env Str) (e env Str))
    ]
    @ (if !ox_mode && on "numbers" then [ (fun () -> num_compare ctx env e) ] else [])
    @ List.map
        (fun op () ->
           let s = fo_env_ty ctx env in
           p "(%s %s %s)" (e env s) op (e env s))
        [ "="; "<>"; "<"; "<="; ">"; ">=" ]
    @ [ (fun () ->
          let s = fo_env_ty ctx env in
          p "(List.mem %s %s)" (e env s) (e env (List s)))
      ; (fun () ->
          let s = env_ty ctx env elem in
          let x = fresh ctx "x" in
          p
            "(List.exists (fun (%s : %s) -> %s) %s)"
            x
            (show_ty s)
            (e (bind (closure env) x s) Bool)
            (e env (List s)))
      ]
  | Float ->
    List.map (fun op -> bin op Float) [ "+."; "-."; "/." ]
    (* opaque so arm64 cannot fuse the product into an fmadd, which rounds differently from ocamlc *)
    @ [ (fun () -> p "(Sys.opaque_identity (%s *. %s))" (e env Float) (e env Float)) ]
    @ List.map
        (fun f -> call f [ Float ])
        [ "sqrt"; "abs_float"; "floor"; "ceil"; "Float.trunc"; "Float.round"; "(~-.)" ]
    @ List.map
        (fun f -> call f [ Float; Float ])
        [ "Float.min"; "Float.max"; "Float.rem" ]
    @ [ call "Float.of_int" [ Int ]; call "Float.fma" [ Float; Float; Float ] ]
    @ (if !ox_mode then [ call "box_float" [ float_u ] ] else [])
    @ if !ox_mode && on "numbers" then [ List.hd (num_ops ctx env Float e) ] else []
  | Char ->
    [ (fun () -> p "(Char.chr (%s land 255))" (e env Int))
    ; call "Char.lowercase_ascii" [ Char ]
    ; call "Char.uppercase_ascii" [ Char ]
    ; (fun () -> p "(Char.unsafe_chr (Char.code %s))" (e env Char))
    ; (fun () -> str_load ctx env e Char)
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
      ; (fun () -> str_load ctx env e Int64)
      ; (fun () -> p "(Int64.div %s %s)" (e env Int64) (int64_lit (nonzero64 ctx)))
      ; (fun () -> p "(Int64.rem %s %s)" (e env Int64) (int64_lit (nonzero64 ctx)))
      ; (fun () ->
          let op =
            choose
              ctx
              (List.map
                 (fun o () -> o)
                 [ "Int64.shift_left"; "Int64.shift_right"; "Int64.shift_right_logical" ])
          in
          p "(%s %s (%s land 63))" op (e env Int64) (e env Int))
      ]
    @ if !ox_mode && on "numbers" then [ List.hd (num_ops ctx env Int64 e) ] else []
  | Str ->
    [ bin "^" Str
    ; call "ssub" [ Str; Int; Int ]
    ; call "string_of_int" [ Int ]
    ; call "Int64.to_string" [ Int64 ]
    ; call "String.uppercase_ascii" [ Str ]
    ; call "String.escaped" [ Str ]
    ; call "String.trim" [ Str ]
    ; call "(String.make 1)" [ Char ]
    ; (fun () -> p "(String.make (%s land 7) %s)" (e env Int) (e env Char))
    ; (fun () -> p "(String.concat %s %s)" (e env Str) (e env (List Str)))
    ; (fun () ->
        let i = fresh ctx "i" in
        p
          "(String.init (%s land 7) (fun (%s : int) -> %s))"
          (e env Int)
          i
          (e (bind (closure env) i Int) Char))
    ; (fun () ->
        let c = fresh ctx "c" in
        p
          "(String.map (fun (%s : char) -> %s) %s)"
          c
          (e (bind (closure env) c Char) Char)
          (e env Str))
    ; (fun () ->
        let b = fresh ctx "b" in
        let i = fresh ctx "i" in
        let env' = bind env i Int in
        p
          "(let %s = Bytes.of_string %s in for %s = 0 to (%s land 7) do if Bytes.length \
           %s > 0 then Bytes.unsafe_set %s ((%s land max_int) mod Bytes.length %s) %s \
           done; Bytes.to_string %s)"
          b
          (e env Str)
          i
          (e env Int)
          b
          b
          (e env' Int)
          b
          (e env' Char)
          b)
    ; (fun () ->
        let b = fresh ctx "b" in
        let i = fresh ctx "i" in
        let env' = bind env i Int in
        p
          "(let %s = Buffer.create (%s land 15) in for %s = 0 to (%s land 7) do \
           Buffer.add_string %s %s; Buffer.add_char %s %s done; Buffer.contents %s)"
          b
          (e env Int)
          i
          (e env Int)
          b
          (e env' Str)
          b
          (e env' Char)
          b)
    ; (fun () ->
        let s = fresh ctx "s" in
        let b = fresh ctx "b" in
        let off = p "((%s land max_int) mod (String.length %s + 1))" (e env Int) s in
        let store =
          choose
            ctx
            [ (fun () -> p "Bytes.set_uint8 %s %s %s" b off (e env Int))
            ; (fun () -> p "Bytes.set_int16_le %s %s %s" b off (e env Int))
            ; (fun () -> p "Bytes.set_uint16_be %s %s %s" b off (e env Int))
            ; (fun () -> p "Bytes.set_int32_le %s %s (Int32.of_int %s)" b off (e env Int))
            ; (fun () -> p "Bytes.set_int32_be %s %s (Int32.of_int %s)" b off (e env Int))
            ; (fun () -> p "Bytes.set_int64_le %s %s %s" b off (e env Int64))
            ; (fun () -> p "Bytes.set_int64_be %s %s %s" b off (e env Int64))
            ]
        in
        p
          "(let %s = %s in let %s = Bytes.of_string (%s ^ \"\\001\\002\\003\\004\\005\\006\\007\\008\") in %s; \
           Bytes.to_string %s)"
          s
          (e env Str)
          b
          s
          store
          b)
    ]
  | U UF ->
    List.map
      (fun f -> call f [ float_u; float_u ])
      [ "fu_add"; "fu_sub"; "fu_mul"; "fu_div" ]
    @ [ call "fu_sqrt" [ float_u ]; call "unbox_float" [ Float ] ]
    @ if on "numbers" then num_ops ctx env ty e else []
  | Num _ | U _ -> num_ops ctx env ty e
  | UTuple ts -> [ (fun () -> p "#(%s)" (String.concat ", " (List.map (e env) ts))) ]
  | Or_null t -> [ (fun () -> "Null"); (fun () -> p "(This %s)" (e env t)) ]
  | Arr t ->
    let n () = p "(1 + (%s land 7))" (e env Int) in
    [ (fun () -> p "[| %s |]" (String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> e env t))))
    ; (fun () -> p "(array_make %s %s)" (n ()) (e env t))
    ; (fun () ->
        (* each index comes from the loop, so it is in bounds *)
        let a = fresh ctx "a" in
        let i = fresh ctx "i" in
        let env' = bind (bind env i Int) (p "(array_get %s %s)" a i) t in
        p
          "(let %s = array_make %s %s in for %s = 0 to array_length %s - 1 do array_set %s %s %s done; %s)"
          a
          (n ())
          (e env t)
          i
          a
          a
          i
          (e env' t)
          a)
    ]
    @ (match t with
       | Arr _ ->
         [ (fun () ->
             let i = fresh ctx "i" in
             p "(Array.init %s (fun (%s : int) -> %s))" (n ()) i (e (bind (closure env) i Int) t))
         ]
       | _ -> [])
  | List t ->
    [ (fun () -> p "(%s :: %s)" (e env t) (e env ty))
    ; (fun () -> p "[%s; %s]" (e env t) (e env t))
    ; call "List.rev" [ ty ]
    ; bin "@" ty
    ; (fun () ->
        let s = env_ty ctx env elem in
        let x = fresh ctx "x" in
        p
          "(List.map (fun (%s : %s) -> %s) %s)"
          x
          (show_ty s)
          (e (bind (closure env) x s) t)
          (e env (List s)))
    ; (fun () ->
        let x = fresh ctx "x" in
        p
          "(List.filter (fun (%s : %s) -> %s) %s)"
          x
          (show_ty t)
          (e (bind (closure env) x t) Bool)
          (e env ty))
    ; (fun () ->
        let i = fresh ctx "i" in
        p
          "(List.init (%s land 7) (fun (%s : int) -> %s))"
          (e env Int)
          i
          (e (bind (closure env) i Int) t))
    ]
    @ (if first_order t then [ (fun () -> p "(List.sort compare %s)" (e env ty)) ] else [])
    @ boost (if on "tmc" then [ (fun () -> tmc ctx env t e) ] else [])
  | Option t ->
    [ (fun () -> p "(Some %s)" (e env t))
    ; (fun () ->
        let x = fresh ctx "x" in
        p
          "(List.find_opt (fun (%s : %s) -> %s) %s)"
          x
          (show_ty t)
          (e (bind (closure env) x t) Bool)
          (e env (List t)))
    ; (fun () ->
        let s =
          env_ty ctx env (function
            | Option s -> Some s
            | _ -> None)
        in
        let x = fresh ctx "x" in
        p
          "(Option.map (fun (%s : %s) -> %s) %s)"
          x
          (show_ty s)
          (e (bind (closure env) x s) t)
          (e env (Option s)))
    ]
  | Pair (a, b) -> [ (fun () -> p "(%s, %s)" (e env a) (e env b)) ]
  | Arrow (a, b) ->
    [ (fun () ->
        let x = fresh ctx "x" in
        p "(fun (%s : %s) -> %s)" x (show_ty a) (e (bind (escape env) x a) b))
    ]
  | Named i ->
    (match ctx.decls.(i) with
     | URecord fields ->
       let build () = String.concat "; " (List.map (fun (f, t) -> p "%s = %s" f (e env t)) fields) in
       [ (fun () -> p "#{ %s }" (build ()))
       ; (fun () ->
           let f, t = List.nth fields (int_in ctx 0 (List.length fields - 1)) in
           p "#{ %s with %s = %s }" (e env ty) f (e env t))
       ]
       @ List.filter_map
           (fun (b, u) ->
              if u <> i
              then None
              else
                Some
                  (fun () ->
                    let s = fresh ctx "s" in
                    p
                      "(let %s = %s in #{ %s })"
                      s
                      (e env (Named b))
                      (String.concat "; " (List.map (fun (f, _) -> p "%s = %s.%s" f s (String.sub f 1 (String.length f - 1))) fields))))
           !twins
     | Variant constrs ->
       List.map (fun (c, args) () -> construct c (List.map (e env) args)) constrs
       @ List.concat_map
           (fun (child, parent) ->
              if child = i
              then (
                let up () = p "(%s : t%d :> t%d)" (e env (Named parent)) parent child in
                [ up; up; up ])
              else [])
           !poly_parent
     | Record fields ->
       let build () =
         String.concat "; " (List.map (fun (f, t, _) -> p "%s = %s" f (e env t)) fields)
       in
       [ (fun () -> p "{ %s }" (build ()))
       ; (fun () ->
           let f, t, _ = List.nth fields (int_in ctx 0 (List.length fields - 1)) in
           p "{ %s with %s = %s }" (e env ty) f (e env t))
       ]
       @ List.filter_map
           (fun (b, u) ->
              if b <> i
              then None
              else
                Some
                  (fun () ->
                    let s = fresh ctx "s" in
                    p
                      "(let %s = %s in { %s })"
                      s
                      (e env (Named u))
                      (String.concat "; " (List.map (fun (f, _, _) -> p "%s = %s.#u%s" f s f) fields))))
           !twins
       @
       (* Only a record the expression allocates is mutated, and only before it
          is returned. *)
       (match List.filter (fun (_, _, m) -> m) fields with
         | [] -> []
         | mutables ->
           [ (fun () ->
               let r = fresh ctx "r" in
               let i = fresh ctx "i" in
               let f, t, _ =
                 List.nth mutables (int_in ctx 0 (List.length mutables - 1))
               in
               let env' =
                 List.fold_left
                   (fun env (g, gt, _) -> bind env (p "%s.%s" r g) gt)
                   (bind env i Int)
                   fields
               in
               p
                 "(let %s = { %s } in for %s = 0 to (%s land 7) do %s.%s <- %s done; %s)"
                 r
                 (build ())
                 i
                 (e env Int)
                 r
                 f
                 (e env' t)
                 r)
           ]))
;;
