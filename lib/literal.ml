open Hegel
open Ty
open Ctx
open Gen_ty

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
        let k = int_in ctx 0 61 in
        paren (string_of_int ((1 lsl k) + int_in ctx (-1) 1)))
    ; (fun () -> paren (string_of_int (draw_silent ctx.tc (integers ()))))
    ]
;;

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
          (p "%h" (draw_silent ctx.tc (floats ~allow_nan:false ~allow_infinity:false ()))))
    ; (fun () -> p "(Int64.float_of_bits %s)" (float_bits ctx))
    ]

(* Bit patterns at the edges: subnormals, the largest finite value, powers of
   two a bit off, and NaNs with payloads. *)
and float_bits ctx =
  let edge =
    [ 1L; 0x000fffffffffffffL; 0x0010000000000000L; 0x7fefffffffffffffL; 0x7ff0000000000000L
    ; 0x7ff0000000000001L; 0x7ff8000000000001L; 0x3ff0000000000000L
    ; Int64.bits_of_float (Float.ldexp 1. (int_in ctx (-1074) 1023))
    ]
  in
  let bits =
    Int64.add
      (List.nth edge (int_in ctx 0 (List.length edge - 1)))
      (Int64.of_int (int_in ctx (-1) 1))
  in
  let bits = if draw_silent ctx.tc (booleans ()) then Int64.logor bits Int64.min_int else bits in
  if Int64.compare bits 0L < 0 then p "(%LdL)" bits else p "%LdL" bits
;;

let float32_bits ctx =
  let edge = [ 1l; 0x007fffffl; 0x00800000l; 0x7f7fffffl; 0x7f800000l; 0x7f800001l; 0x7fc00001l; 0x3f800000l ] in
  let bits =
    Int32.add (List.nth edge (int_in ctx 0 (List.length edge - 1))) (Int32.of_int (int_in ctx (-1) 1))
  in
  let bits = if draw_silent ctx.tc (booleans ()) then Int32.logor bits Int32.min_int else bits in
  if Int32.compare bits 0l < 0 then p "(%ldl)" bits else p "%ldl" bits
;;

(* A literal of a new number type: an integer in its range or a float32,
   unboxed with # when the syntax allows and by conversion otherwise. *)
let num_literal ctx t =
  let w = width t in
  let int_value () =
    let lo = if w = 64 then Int64.min_int else Int64.neg (Int64.shift_left 1L (w - 1)) in
    let hi = if w = 64 then Int64.max_int else Int64.pred (Int64.shift_left 1L (w - 1)) in
    choose
      ctx
      [ (fun () -> 0L)
      ; (fun () -> 1L)
      ; (fun () -> -1L)
      ; (fun () -> Int64.of_int (int_in ctx (-100) 100))
      ; (fun () -> lo)
      ; (fun () -> hi)
      ; (fun () -> Int64.shift_left 1L (int_in ctx 0 (w - 2)))
      ; (fun () ->
          let x = Int64.of_int (draw_silent ctx.tc (integers ())) in
          if w = 64 then x else Int64.rem x (Int64.shift_left 1L (w - 1)))
      ]
  in
  let suffix = function
    | Num I8 | U UI8 -> "s"
    | Num I16 | U UI16 -> "S"
    | Num I32 | U UI32 -> "l"
    | Num Nat | U UNat -> "n"
    | Int64 | U UI64 -> "L"
    | _ -> ""
  in
  let f32 () =
    choose
      ctx
      [ (fun () -> p "(F32.of_float %s)" (float_literal ctx))
      ; (fun () -> p "(F32.of_bits %s)" (float32_bits ctx))
      ]
  in
  match t with
  | Num F32 -> f32 ()
  | U UF32 -> convert (Num F32) t (f32 ())
  | U UF -> convert Float t (float_literal ctx)
  | U UI -> convert Int t (paren (Int64.to_string (int_value ())))
  | Num _ ->
    let v = int_value () in
    paren (Int64.to_string v ^ suffix t)
  | U _ ->
    let v = int_value () in
    if Int64.compare v 0L >= 0
    then p "#%Ld%s" v (suffix t)
    else convert (boxed_of t) t (paren (Int64.to_string v ^ suffix (boxed_of t)))
  | _ -> invalid_arg "num_literal"
;;

let char_literal ctx =
  choose
    ctx
    [ (fun () -> "'a'")
    ; (fun () -> p "%C" (Char.chr (int_in ctx (Char.code 'a') (Char.code 'h'))))
    ; (fun () -> p "%C" (Char.chr (int_in ctx 0 255)))
    ]
;;

let int64_lit n = if Int64.compare n 0L < 0 then p "(%LdL)" n else p "%LdL" n

let int64_literal ctx =
  choose
    ctx
    [ (fun () -> "0L")
    ; (fun () -> int64_lit (Int64.of_int (int_in ctx (-2) 5)))
    ; (fun () -> "Int64.max_int")
    ; (fun () -> "Int64.min_int")
    ; (fun () -> "(-1L)")
    ; (fun () -> int64_lit (Int64.shift_left 1L (int_in ctx 0 63)))
    ; (fun () ->
        int64_lit
          (Int64.logor
             (Int64.shift_left (Int64.of_int (draw_silent ctx.tc (integers ()))) 1)
             (Int64.of_int (int_in ctx 0 1))))
    ]
;;

let string_literal ctx =
  let n = int_in ctx 0 8 in
  p
    "%S"
    (String.init n (fun _ ->
       if draw_silent ctx.tc (booleans ~p:0.2 ())
       then Char.chr (int_in ctx 0 255)
       else Char.chr (int_in ctx (Char.code 'a') (Char.code 'e'))))
;;

let rec literal ctx ty =
  match ty with
  | Int -> int_literal ctx
  | Bool -> if draw_silent ctx.tc (booleans ()) then "true" else "false"
  | Float -> float_literal ctx
  | Char -> char_literal ctx
  | Int64 -> int64_literal ctx
  | Str -> string_literal ctx
  | List t ->
    choose
      ctx
      [ (fun () -> "[]")
      ; (fun () -> p "[%s]" (literal ctx t))
      ; (fun () -> p "[%s; %s; %s]" (literal ctx t) (literal ctx t) (literal ctx t))
      ]
  | Option t ->
    if draw_silent ctx.tc (booleans ()) then p "(Some %s)" (literal ctx t) else "None"
  | Pair (a, b) -> p "(%s, %s)" (literal ctx a) (literal ctx b)
  | Arrow (a, b) -> p "(fun (_ : %s) -> %s)" (show_ty a) (literal ctx b)
  | U UF ->
    choose
      ctx
      [ (fun () -> "#0.")
      ; (fun () -> "#1.")
      ; (fun () -> "#0x1.8p+1")
      ; (fun () -> p "(unbox_float %s)" (float_literal ctx))
      ]
  | Num _ | U _ -> num_literal ctx ty
  | UTuple ts -> p "#(%s)" (String.concat ", " (List.map (literal ctx) ts))
  | Or_null t ->
    if draw_silent ctx.tc (booleans ()) then p "(This %s)" (literal ctx t) else "Null"
  | Arr t -> p "[| %s |]" (String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> literal ctx t)))
  | Named i ->
    (match ctx.decls.(i) with
     | Record fields ->
       p
         "{ %s }"
         (String.concat
            "; "
            (List.map (fun (f, t, _) -> p "%s = %s" f (literal ctx t)) fields))
     | Variant constrs ->
       let c, args = List.nth constrs (int_in ctx 0 (List.length constrs - 1)) in
       construct c (List.map (literal ctx) args)
     | URecord fields ->
       p "#{ %s }" (String.concat "; " (List.map (fun (f, t) -> p "%s = %s" f (literal ctx t)) fields)))

and construct c = function
  | [] -> c
  | args -> p "(%s (%s))" c (String.concat ", " args)
;;

(* [raise Exit] at any type; raise itself only returns a value. *)
let rec raise_at ctx ty =
  match ty with
  | U UF -> "(unbox_float (raise Exit))"
  | U _ -> convert (boxed_of ty) ty "(raise Exit)"
  | UTuple ts -> p "#(%s)" (String.concat ", " (List.map (raise_at ctx) ts))
  | Or_null _ -> "(This (raise Exit))"
  | Named i ->
    (match ctx.decls.(i) with
     | URecord fields ->
       p "#{ %s }" (String.concat "; " (List.map (fun (f, t) -> p "%s = %s" f (raise_at ctx t)) fields))
     | _ -> "(raise Exit)")
  | _ -> "(raise Exit)"
;;
