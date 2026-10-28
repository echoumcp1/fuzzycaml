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
  (* OxCaml only. Unboxed values (U, UTuple, Or_null and unboxed records) are
     only bound, passed, returned or stored in a record, tuple or array that
     allows them, never in a list, option or pair. *)
  | Num of nb
  | U of ub
  | UTuple of ty list
  | Or_null of ty
  | Arr of ty

and nb = I8 | I16 | I32 | Nat | F32
and ub = UF | UF32 | UI | UI8 | UI16 | UI32 | UI64 | UNat

let float_u = U UF

(* Declared types refer only to earlier ones and hold only first-order
   values. *)
type decl =
  | Record of (string * ty * bool) list (* name, type, mutable *)
  | Variant of (string * ty list) list
  | URecord of (string * ty) list

let num_name = function
  | Int -> "int"
  | Int64 -> "int64"
  | Float -> "float"
  | Num I8 -> "int8"
  | Num I16 -> "int16"
  | Num I32 -> "int32"
  | Num Nat -> "nativeint"
  | Num F32 -> "float32"
  | U UF -> "float#"
  | U UF32 -> "float32#"
  | U UI -> "int#"
  | U UI8 -> "int8#"
  | U UI16 -> "int16#"
  | U UI32 -> "int32#"
  | U UI64 -> "int64#"
  | U UNat -> "nativeint#"
  | _ -> invalid_arg "num_name"
;;

let is_num = function
  | Int | Int64 | Float | Num _ | U _ -> true
  | _ -> false
;;

let is_float = function
  | Float | Num F32 | U UF | U UF32 -> true
  | _ -> false
;;

let width = function
  | Int | U UI -> 63
  | Num I8 | U UI8 -> 8
  | Num I16 | U UI16 -> 16
  | Num I32 | U UI32 -> 32
  | _ -> 64
;;

(* The module with each number type's arithmetic, aliased in the prelude. *)
let num_module = function
  | Int -> "Int"
  | Int64 -> "Int64"
  | Float -> "Float"
  | Num I8 -> "I8"
  | Num I16 -> "I16"
  | Num I32 -> "Int32"
  | Num Nat -> "Nativeint"
  | Num F32 -> "F32"
  | U UF -> "Fu"
  | U UF32 -> "F32u"
  | U UI -> "Iu"
  | U UI8 -> "I8u"
  | U UI16 -> "I16u"
  | U UI32 -> "I32u"
  | U UI64 -> "I64u"
  | U UNat -> "Natu"
  | _ -> invalid_arg "num_module"
;;

let boxed_of = function
  | U UF -> Float
  | U UF32 -> Num F32
  | U UI -> Int
  | U UI8 -> Num I8
  | U UI16 -> Num I16
  | U UI32 -> Num I32
  | U UI64 -> Int64
  | U UNat -> Num Nat
  | t -> t
;;

let all_nb = [ I8; I16; I32; Nat; F32 ]
let all_ub = [ UF; UF32; UI; UI8; UI16; UI32; UI64; UNat ]
let newer_nums = List.map (fun n -> Num n) all_nb @ List.map (fun u -> U u) all_ub

(* Number conversions are externals, declared at the top of the program as they
   are used. Float-to-integer conversions saturate, since out-of-range results
   are unspecified. *)
let convs = ref []

let conv_ext a b =
  let clean t = String.map (fun c -> if c = '#' then 'u' else c) (num_name t) in
  let name = Printf.sprintf "cv_%s_%s" (clean a) (clean b) in
  if not (List.mem_assoc name !convs) then convs := (name, (a, b)) :: !convs;
  name
;;

let convert a b x =
  if a = b
  then x
  else if is_float a && not (is_float b)
  then (
    let f = if a = Float then x else Printf.sprintf "(%s %s)" (conv_ext a Float) x in
    let i = Printf.sprintf "(fsat %d %s)" (width b) f in
    if b = Int64 then i else Printf.sprintf "(%s %s)" (conv_ext Int64 b) i)
  else Printf.sprintf "(%s %s)" (conv_ext a b) x
;;

let rec show_ty = function
  | Int -> "int"
  | Bool -> "bool"
  | Float -> "float"
  | Char -> "char"
  | Int64 -> "int64"
  | Str -> "string"
  | List t -> Printf.sprintf "(%s list)" (show_ty t)
  | Option t -> Printf.sprintf "(%s option)" (show_ty t)
  | Pair (a, b) -> Printf.sprintf "(%s * %s)" (show_ty a) (show_ty b)
  | Arrow (a, b) -> Printf.sprintf "(%s -> %s)" (show_ty a) (show_ty b)
  | Named i -> Printf.sprintf "t%d" i
  | Num I32 -> "int32"
  | Num Nat -> "nativeint"
  | U UF -> "float#"
  | (Num _ | U _) as t -> num_module t ^ ".t"
  | UTuple ts -> Printf.sprintf "#(%s)" (String.concat " * " (List.map show_ty ts))
  | Or_null t -> Printf.sprintf "(%s or_null)" (show_ty t)
  | Arr t -> Printf.sprintf "(%s array)" (show_ty t)
;;

(* float32 is not first-order, to avoid polymorphic comparison of float32 NaNs.
   *)
let rec first_order = function
  | Int | Bool | Float | Char | Int64 | Str | Num (I8 | I16 | I32 | Nat) -> true
  | Named i -> not !mixed.(i)
  | Num F32 | U _ | UTuple _ | Or_null _ | Arr _ -> false
  | List t | Option t -> first_order t
  | Pair (a, b) -> first_order a && first_order b
  | Arrow _ -> false
;;

(* Whether a value of the type can only be bound, passed, returned, or held
   by an unboxed tuple or record or a record field. *)
let restricted = function
  | U _ | UTuple _ | Or_null _ -> true
  | Named i -> !urec.(i)
  | _ -> false
;;

let rec has_float_u t =
  match t with
  | Named i -> !mixed.(i)
  | List t | Option t -> has_float_u t
  | Pair (a, b) -> has_float_u a || has_float_u b
  | t -> not (first_order t) && (match t with Arrow _ -> false | _ -> true)
;;
