open Hegel
open Config
open Ty
open Ctx

let int_literal ctx =
  choose
    ctx
    [ (fun () -> "0")
    ; (fun () -> paren (string_of_int (int_in ctx (-2) 5)))
    ; (fun () -> "1")
    ; (fun () -> "(-1)")
    ; (fun () -> paren (string_of_int (int_in ctx (-100) 100)))
    ; (fun () -> "max_int")
    ; (fun () -> "min_int")
    ; (fun () ->
        let shift = int_in ctx 0 61 in
        paren (string_of_int ((1 lsl shift) + int_in ctx (-1) 1)))
    ; (fun () -> paren (string_of_int (Draw.unbounded ctx.tc)))
    ]
;;

let show_int64 n = paren (Printf.sprintf "%LdL" n)

let rec float_literal ctx =
  choose
    ctx
    [ (fun () -> "0.")
    ; (fun () -> "1.")
    ; (fun () -> "(-0.)")
    ; (fun () -> "nan")
    ; (fun () -> "infinity")
    ; (fun () -> "neg_infinity")
    ; (fun () -> "max_float")
    ; (fun () -> "min_float")
    ; (fun () -> "epsilon_float")
    ; (fun () -> "0x0.0000000000001p-1022")
    ; (fun () ->
        paren
          (Printf.sprintf
             "%h"
             (Draw.float ctx.tc (floats ~allow_nan:false ~allow_infinity:false ()))))
    ; (fun () -> [%string "(Int64.float_of_bits %{float_bits ctx})"])
    ]

and float_bits ctx =
  let edge =
    [ 1L
    ; 0x000fffffffffffffL
    ; 0x0010000000000000L
    ; 0x7fefffffffffffffL
    ; 0x7ff0000000000000L
    ; 0x7ff0000000000001L
    ; 0x7ff8000000000001L
    ; 0x3ff0000000000000L
    ; Int64.bits_of_float (Float.ldexp 1. (int_in ctx (-1074) 1023))
    ]
  in
  let bits = Int64.add (pick ctx edge) (Int64.of_int (int_in ctx (-1) 1)) in
  show_int64 (if flip ctx then Int64.logor bits Int64.min_int else bits)
;;

let float32_bits ctx =
  let edge =
    [ 1l
    ; 0x007fffffl
    ; 0x00800000l
    ; 0x7f7fffffl
    ; 0x7f800000l
    ; 0x7f800001l
    ; 0x7fc00001l
    ; 0x3f800000l
    ]
  in
  let bits = Int32.add (pick ctx edge) (Int32.of_int (int_in ctx (-1) 1)) in
  paren
    (Printf.sprintf "%ldl" (if flip ctx then Int32.logor bits Int32.min_int else bits))
;;

let num_literal ctx num_ty =
  let bit_width = width num_ty in
  let int_value () =
    let min =
      if bit_width = 64
      then Int64.min_int
      else Int64.neg (Int64.shift_left 1L (bit_width - 1))
    in
    let max =
      if bit_width = 64
      then Int64.max_int
      else Int64.pred (Int64.shift_left 1L (bit_width - 1))
    in
    choose
      ctx
      [ (fun () -> 0L)
      ; (fun () -> 1L)
      ; (fun () -> -1L)
      ; (fun () -> Int64.of_int (int_in ctx (-100) 100))
      ; (fun () -> min)
      ; (fun () -> max)
      ; (fun () -> Int64.shift_left 1L (int_in ctx 0 (bit_width - 2)))
      ; (fun () ->
          let drawn = Int64.of_int (Draw.unbounded ctx.tc) in
          if bit_width = 64
          then drawn
          else Int64.rem drawn (Int64.shift_left 1L (bit_width - 1)))
      ]
  in
  let suffix = function
    | Num I8 | Unboxed UInt8 -> "s"
    | Num I16 | Unboxed UInt16 -> "S"
    | Num I32 | Unboxed UInt32 -> "l"
    | Num Nat | Unboxed UNativeint -> "n"
    | Int64 | Unboxed UInt64 -> "L"
    | _ -> ""
  in
  (* Small integer literals are an extension, so they are erased to a
     conversion. *)
  let boxed num_ty value =
    match num_ty with
    | Num ((I8 | I16) as small) when !erase ->
      [%string "(%{num_module (Num small)}.of_int %{paren (Int64.to_string value)})"]
    | _ -> paren (Int64.to_string value ^ suffix num_ty)
  in
  let float32_literal () =
    choose
      ctx
      [ (fun () -> [%string "(F32.of_float %{float_literal ctx})"])
      ; (fun () -> [%string "(F32.of_bits %{float32_bits ctx})"])
      ]
  in
  match num_ty with
  | Num F32 -> float32_literal ()
  | Unboxed UFloat32 -> convert (Num F32) num_ty (float32_literal ())
  | Unboxed UFloat -> convert Float num_ty (float_literal ctx)
  | Unboxed UInt -> convert Int num_ty (paren (Int64.to_string (int_value ())))
  | Num _ ->
    let value = int_value () in
    boxed num_ty value
  | Unboxed _ ->
    let value = int_value () in
    if Int64.compare value 0L >= 0 && not !erase
    then Printf.sprintf "#%Ld%s" value (suffix num_ty)
    else convert (boxed_of num_ty) num_ty (boxed (boxed_of num_ty) value)
  | _ -> invalid_arg "num_literal"
;;

let char_literal ctx =
  choose
    ctx
    [ (fun () -> "'a'")
    ; (fun () ->
        Printf.sprintf "%C" (Char.chr (int_in ctx (Char.code 'a') (Char.code 'h'))))
    ; (fun () -> Printf.sprintf "%C" (Char.chr (int_in ctx 0 255)))
    ]
;;

let int64_literal ctx =
  choose
    ctx
    [ (fun () -> "0L")
    ; (fun () -> show_int64 (Int64.of_int (int_in ctx (-2) 5)))
    ; (fun () -> "Int64.max_int")
    ; (fun () -> "Int64.min_int")
    ; (fun () -> "(-1L)")
    ; (fun () -> show_int64 (Int64.shift_left 1L (int_in ctx 0 63)))
    ; (fun () ->
        show_int64
          (Int64.logor
             (Int64.shift_left (Int64.of_int (Draw.unbounded ctx.tc)) 1)
             (Int64.of_int (int_in ctx 0 1))))
    ]
;;

let string_literal ctx =
  let n = int_in ctx 0 8 in
  Printf.sprintf
    "%S"
    (String.init n (fun _ ->
       if flip ~p:0.2 ctx
       then Char.chr (int_in ctx 0 255)
       else Char.chr (int_in ctx (Char.code 'a') (Char.code 'e'))))
;;

let utuple xs = ox_syntax "#" "" ^ "(" ^ String.concat ", " xs ^ ")"
let this x = "(" ^ ox_syntax "This " "Some " ^ x ^ ")"
let null () = ox_syntax "Null" "None"
let urecord fields = ox_syntax "#" "" ^ "{ " ^ fields ^ " }"

let nonzero64 ctx =
  choose
    ctx
    [ (fun () -> 1L)
    ; (fun () -> -1L)
    ; (fun () -> Int64.shift_left 1L (int_in ctx 0 62))
    ; (fun () -> Int64.of_int (int_in ctx 2 1000))
    ; (fun () -> Int64.min_int)
    ; (fun () -> Int64.of_int (-int_in ctx 2 1000))
    ]
;;

let nonzero ctx =
  choose
    ctx
    [ (fun () -> "1")
    ; (fun () -> "(-1)")
    ; (fun () -> "2")
    ; (fun () -> paren (string_of_int (1 lsl int_in ctx 0 61)))
    ; (fun () ->
        let n = int_in ctx (-1000) 1000 in
        paren (string_of_int (if n = 0 then 7 else n)))
    ; (fun () -> "max_int")
    ; (fun () -> "min_int")
    ; (fun () ->
        let n = Draw.unbounded ctx.tc in
        paren (string_of_int (if n = 0 then 3 else n)))
    ]
;;

let rec literal ctx ty =
  match ty with
  | Int -> int_literal ctx
  | Bool -> string_of_bool (flip ctx)
  | Float -> float_literal ctx
  | Char -> char_literal ctx
  | Int64 -> int64_literal ctx
  | Str -> string_literal ctx
  | List elem_ty ->
    choose
      ctx
      [ (fun () -> "[]")
      ; (fun () -> [%string "[%{literal ctx elem_ty}]"])
      ; (fun () ->
          [%string
            "[%{literal ctx elem_ty}; %{literal ctx elem_ty}; %{literal ctx elem_ty}]"])
      ]
  | Option elem_ty ->
    if flip ctx then [%string "(Some %{literal ctx elem_ty})"] else "None"
  | Pair (first, second) -> [%string "(%{literal ctx first}, %{literal ctx second})"]
  | Arrow (first, second) when (not !quiet) && same_repr first && flip ctx ->
    (* So that the argument decides the result. *)
    [%string
      "(fun (x : %{first#Ty}) -> if Hashtbl.hash x land 1 = 0 then %{literal ctx second} \
       else %{literal ctx second})"]
  | Arrow (first, second) -> [%string "(fun (_ : %{first#Ty}) -> %{literal ctx second})"]
  | Unboxed UFloat ->
    choose
      ctx
      [ (fun () -> ox_syntax "#0." "0.")
      ; (fun () -> ox_syntax "#1." "1.")
      ; (fun () -> ox_syntax "#0x1.8p+1" "0x1.8p+1")
      ; (fun () -> [%string "(unbox_float %{float_literal ctx})"])
      ]
  | Num _ | Unboxed _ -> num_literal ctx ty
  | UTuple ts -> utuple (List.map (literal ctx) ts)
  | Or_null elem_ty -> if flip ctx then this (literal ctx elem_ty) else null ()
  | Arr elem_ty ->
    let elems =
      String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> literal ctx elem_ty))
    in
    [%string "[| %{elems} |]"]
  | Named decl ->
    (match ctx.decls.(decl) with
     | Record fields -> [%string "{ %{field_values (literal ctx) (field_types fields)} }"]
     | Variant constrs ->
       let constructor, args = pick ctx constrs in
       construct constructor (List.map (literal ctx) args)
     | URecord fields -> urecord (field_values (literal ctx) fields))

and construct constructor = function
  | [] -> constructor
  | args when List.mem constructor !inline_records ->
    let fields = List.mapi (fun index arg -> [%string "r%{index#Int} = %{arg}"]) args in
    [%string {|(%{constructor} { %{String.concat "; " fields} })|}]
  | args -> [%string {|(%{constructor} (%{String.concat ", " args}))|}]
;;

(* [raise Exit] at any type. raise only has value types, so unboxed results are
   built around it. *)
let rec raise_at ctx ty =
  match ty with
  | Unboxed UFloat -> "(unbox_float (raise Exit))"
  | Unboxed _ -> convert (boxed_of ty) ty "(raise Exit)"
  | UTuple ts -> utuple (List.map (raise_at ctx) ts)
  | Or_null _ -> this "(raise Exit)"
  | Named i ->
    (match ctx.decls.(i) with
     | URecord fields -> urecord (field_values (raise_at ctx) fields)
     | _ -> "(raise Exit)")
  | _ -> "(raise Exit)"
;;
