open Config
open Ty
open Ctx
open Env

(* A string read at an offset inside the string's padding. *)
let string_load ctx env ty expr =
  let str = fresh ctx "s" in
  let offset =
    [%string "((%{expr env Int} land max_int) mod (String.length %{str} + 1))"]
  in
  let padded = [%string "(%{str} ^ \"\\001\\002\\003\\004\\005\\006\\007\\008\")"] in
  let load =
    match ty with
    | Int ->
      choose
        ctx
        [ (fun () -> [%string "String.get_uint8 %{padded} %{offset}"])
        ; (fun () -> [%string "String.get_int8 %{padded} %{offset}"])
        ; (fun () -> [%string "String.get_int16_le %{padded} %{offset}"])
        ; (fun () -> [%string "String.get_uint16_be %{padded} %{offset}"])
        ; (fun () -> [%string "Int32.to_int (String.get_int32_le %{padded} %{offset})"])
        ; (fun () -> [%string "Int32.to_int (String.get_int32_be %{padded} %{offset})"])
        ; (fun () ->
            [%string
              "(if String.length %{str} = 0 then 0 else Char.code (String.unsafe_get \
               %{str} ((%{expr env Int} land max_int) mod String.length %{str})))"])
        ]
    | Int64 ->
      choose
        ctx
        [ (fun () -> [%string "String.get_int64_le %{padded} %{offset}"])
        ; (fun () -> [%string "String.get_int64_be %{padded} %{offset}"])
        ]
    | _ ->
      choose
        ctx
        [ (fun () -> [%string "%{padded}.[%{offset}]"])
        ; (fun () -> [%string "String.unsafe_get %{padded} %{offset}"])
        ]
  in
  [%string "(let %{str} = %{expr env Str} in %{load})"]
;;

(* A match on literals that share prefixes around the 8-byte word, for the
   compiler's string-match code. *)
let string_match ctx env ty expr =
  let letter () = Char.chr (int_in ctx (Char.code 'a') (Char.code 'c')) in
  let base = String.init (int_in ctx 5 17) (fun _ -> letter ()) in
  let length = String.length base in
  let near_base () =
    choose
      ctx
      [ (fun () -> base)
      ; (fun () -> String.sub base 0 (int_in ctx 0 length))
      ; (fun () -> base ^ String.init (int_in ctx 1 3) (fun _ -> letter ()))
      ; (fun () -> String.sub base 0 (length - 1) ^ "z")
      ]
  in
  let literals =
    List.sort_uniq compare (List.init (int_in ctx 1 5) (fun _ -> near_base ()))
  in
  let scrutinee =
    choose
      ctx
      [ (fun () -> expr env Str)
      ; (fun () -> Printf.sprintf "%S" (near_base ()))
      ; (fun () ->
          Printf.sprintf
            "(%S ^ %s)"
            (String.sub base 0 (int_in ctx 0 length))
            (expr env Str))
      ]
  in
  Printf.sprintf
    "(match %s with %s | _ -> %s)"
    scrutinee
    (String.concat
       " "
       (List.map
          (fun literal -> Printf.sprintf "| %S -> %s" literal (expr env ty))
          literals))
    (expr env ty)
;;

let forms ctx env ty gen =
  if on "strings" then [ (fun () -> string_match ctx env ty gen.expr) ] else []
;;
