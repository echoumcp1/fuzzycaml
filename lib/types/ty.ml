open Config

type ty =
  | Int
  | Bool
  | Float
  | Char
  | Int64
  | Str
  | List of ty
  | Option of ty
  | Pair of ty * ty
  | Arrow of ty * ty
  | Named of int
  (* OxCaml only. Unboxed values (Unboxed, UTuple, Or_null and unboxed records)
     are only bound, passed, returned or stored in a record, tuple or array that
     allows them, never in a list, option or pair. *)
  | Num of boxed_number
  | Unboxed of unboxed_number
  | UTuple of ty list
  | Or_null of ty
  | Arr of ty

and boxed_number =
  | I8
  | I16
  | I32
  | Nat
  | F32

and unboxed_number =
  | UFloat
  | UFloat32
  | UInt
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | UNativeint

let unboxed_float = Unboxed UFloat

(* Declared types refer only to earlier ones and hold only first-order
   values. *)
type decl =
  | Record of (string * ty * bool) list
  | Variant of (string * ty list) list
  | URecord of (string * ty) list

let field_types fields = List.map (fun (field, field_ty, _) -> field, field_ty) fields

let num_name = function
  | Int -> "int"
  | Int64 -> "int64"
  | Float -> "float"
  | Num I8 -> "int8"
  | Num I16 -> "int16"
  | Num I32 -> "int32"
  | Num Nat -> "nativeint"
  | Num F32 -> "float32"
  | Unboxed UFloat -> "float#"
  | Unboxed UFloat32 -> "float32#"
  | Unboxed UInt -> "int#"
  | Unboxed UInt8 -> "int8#"
  | Unboxed UInt16 -> "int16#"
  | Unboxed UInt32 -> "int32#"
  | Unboxed UInt64 -> "int64#"
  | Unboxed UNativeint -> "nativeint#"
  | _ -> invalid_arg "num_name"
;;

let is_num = function
  | Int | Int64 | Float | Num _ | Unboxed _ -> true
  | _ -> false
;;

let is_float = function
  | Float | Num F32 | Unboxed UFloat | Unboxed UFloat32 -> true
  | _ -> false
;;

let width = function
  | Int | Unboxed UInt -> 63
  | Num I8 | Unboxed UInt8 -> 8
  | Num I16 | Unboxed UInt16 -> 16
  | Num I32 | Unboxed UInt32 -> 32
  | _ -> 64
;;

let num_module = function
  | Int -> "Int"
  | Int64 -> "Int64"
  | Float -> "Float"
  | Num I8 -> "I8"
  | Num I16 -> "I16"
  | Num I32 -> "Int32"
  | Num Nat -> "Nativeint"
  | Num F32 -> "F32"
  | Unboxed UFloat -> "Fu"
  | Unboxed UFloat32 -> "F32u"
  | Unboxed UInt -> "Iu"
  | Unboxed UInt8 -> "I8u"
  | Unboxed UInt16 -> "I16u"
  | Unboxed UInt32 -> "I32u"
  | Unboxed UInt64 -> "I64u"
  | Unboxed UNativeint -> "Natu"
  | _ -> invalid_arg "num_module"
;;

let boxed_of = function
  | Unboxed UFloat -> Float
  | Unboxed UFloat32 -> Num F32
  | Unboxed UInt -> Int
  | Unboxed UInt8 -> Num I8
  | Unboxed UInt16 -> Num I16
  | Unboxed UInt32 -> Num I32
  | Unboxed UInt64 -> Int64
  | Unboxed UNativeint -> Num Nat
  | t -> t
;;

let boxed_numbers = [ I8; I16; I32; Nat; F32 ]

let unboxed_numbers =
  [ UFloat; UFloat32; UInt; UInt8; UInt16; UInt32; UInt64; UNativeint ]
;;

let newer_numbers =
  List.map (fun n -> Num n) boxed_numbers @ List.map (fun u -> Unboxed u) unboxed_numbers
;;

(* Float-to-integer conversions saturate, since out-of-range results are unspecified. *)
let conversions = ref []

let conversion from_ty to_ty =
  let identifier t = String.map (fun c -> if c = '#' then 'u' else c) (num_name t) in
  let name = [%string "cv_%{identifier from_ty}_%{identifier to_ty}"] in
  if not (List.mem_assoc name !conversions)
  then conversions := (name, (from_ty, to_ty)) :: !conversions;
  name
;;

let convert from_ty to_ty value =
  if from_ty = to_ty
  then value
  else if is_float from_ty && not (is_float to_ty)
  then (
    let as_float =
      if from_ty = Float
      then value
      else [%string "(%{conversion from_ty Float} %{value})"]
    in
    let as_int64 = [%string "(fsat %{width to_ty#Int} %{as_float})"] in
    if to_ty = Int64
    then as_int64
    else [%string "(%{conversion Int64 to_ty} %{as_int64})"])
  else [%string "(%{conversion from_ty to_ty} %{value})"]
;;

let rec show_ty = function
  | Int -> "int"
  | Bool -> "bool"
  | Float -> "float"
  | Char -> "char"
  | Int64 -> "int64"
  | Str -> "string"
  | List t -> [%string "(%{show_ty t} list)"]
  | Option t -> [%string "(%{show_ty t} option)"]
  | Pair (a, b) -> [%string "(%{show_ty a} * %{show_ty b})"]
  | Arrow (a, b) -> [%string "(%{show_ty a} -> %{show_ty b})"]
  | Named i -> [%string "t%{i#Int}"]
  | Num I32 -> "int32"
  | Num Nat -> "nativeint"
  | Unboxed UFloat -> "float#"
  | (Num _ | Unboxed _) as t -> num_module t ^ ".t"
  | UTuple ts -> "#" ^ "(" ^ String.concat " * " (List.map show_ty ts) ^ ")"
  | Or_null t -> "(" ^ show_ty t ^ " or_null)"
  | Arr t -> [%string "(%{show_ty t} array)"]
;;

(* for %{t#Ty} in [%string] *)
let to_string = show_ty

(* float32 is not first-order, to avoid polymorphic comparison of float32 NaNs.
   *)
let rec first_order = function
  | Int | Bool | Float | Char | Int64 | Str | Num (I8 | I16 | I32 | Nat) -> true
  | Named i -> not !not_first_order_decls.(i)
  | Num F32 | Unboxed _ | UTuple _ | Or_null _ | Arr _ -> false
  | List t | Option t -> first_order t
  | Pair (a, b) -> first_order a && first_order b
  | Arrow _ -> false
;;

let restricted = function
  | Unboxed _ | UTuple _ | Or_null _ -> true
  | Named i -> !unboxed_record_decls.(i)
  | _ -> false
;;

let rec has_unboxed t =
  match t with
  | Named i -> !not_first_order_decls.(i)
  | List t | Option t -> has_unboxed t
  | Pair (a, b) -> has_unboxed a || has_unboxed b
  | t ->
    (not (first_order t))
    &&
      (match t with
      | Arrow _ -> false
      | _ -> true)
;;
