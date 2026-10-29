open Hegel
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
        let k = int_in ctx 0 61 in
        paren (string_of_int ((1 lsl k) + int_in ctx (-1) 1)))
    ; (fun () -> paren (string_of_int (draw_silent ctx.tc (integers ()))))
    ]
;;

let int64_lit n = paren (p "%LdL" n)

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
    ; (fun () -> [%string "(Int64.float_of_bits %{float_bits ctx})"])
    ]

(* Edge-case bit patterns: subnormals, the largest finite value, powers of two
   one ulp off, and NaNs with payloads. *)
and float_bits ctx =
  let edge =
    [ 1L; 0x000fffffffffffffL; 0x0010000000000000L; 0x7fefffffffffffffL; 0x7ff0000000000000L
    ; 0x7ff0000000000001L; 0x7ff8000000000001L; 0x3ff0000000000000L
    ; Int64.bits_of_float (Float.ldexp 1. (int_in ctx (-1074) 1023))
    ]
  in
  let bits = Int64.add (pick ctx edge) (Int64.of_int (int_in ctx (-1) 1)) in
  int64_lit (if flip ctx then Int64.logor bits Int64.min_int else bits)
;;

let float32_bits ctx =
  let edge = [ 1l; 0x007fffffl; 0x00800000l; 0x7f7fffffl; 0x7f800000l; 0x7f800001l; 0x7fc00001l; 0x3f800000l ] in
  let bits = Int32.add (pick ctx edge) (Int32.of_int (int_in ctx (-1) 1)) in
  paren (p "%ldl" (if flip ctx then Int32.logor bits Int32.min_int else bits))
;;

(* A literal of a newer number type: an integer in its range or a float32,
   unboxed with # where the syntax allows and by conversion otherwise. *)
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
      [ (fun () -> [%string "(F32.of_float %{float_literal ctx})"])
      ; (fun () -> [%string "(F32.of_bits %{float32_bits ctx})"])
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
       if flip ~p:0.2 ctx
       then Char.chr (int_in ctx 0 255)
       else Char.chr (int_in ctx (Char.code 'a') (Char.code 'e'))))
;;

let rec literal ctx ty =
  match ty with
  | Int -> int_literal ctx
  | Bool -> string_of_bool (flip ctx)
  | Float -> float_literal ctx
  | Char -> char_literal ctx
  | Int64 -> int64_literal ctx
  | Str -> string_literal ctx
  | List t ->
    choose
      ctx
      [ (fun () -> "[]")
      ; (fun () -> [%string "[%{literal ctx t}]"])
      ; (fun () -> [%string "[%{literal ctx t}; %{literal ctx t}; %{literal ctx t}]"])
      ]
  | Option t ->
    if flip ctx then [%string "(Some %{literal ctx t})"] else "None"
  | Pair (a, b) -> [%string "(%{literal ctx a}, %{literal ctx b})"]
  | Arrow (a, b) -> [%string "(fun (_ : %{show_ty a}) -> %{literal ctx b})"]
  | U UF ->
    choose
      ctx
      [ (fun () -> "#0.")
      ; (fun () -> "#1.")
      ; (fun () -> "#0x1.8p+1")
      ; (fun () -> [%string "(unbox_float %{float_literal ctx})"])
      ]
  | Num _ | U _ -> num_literal ctx ty
  | UTuple ts -> [%string {|#(%{String.concat ", " (List.map (literal ctx) ts)})|}]
  | Or_null t ->
    if flip ctx then [%string "(This %{literal ctx t})"] else "Null"
  | Arr t -> p "[| %s |]" (String.concat "; " (List.init (int_in ctx 1 3) (fun _ -> literal ctx t)))
  | Named i ->
    (match ctx.decls.(i) with
     | Record fields ->
       p
         "{ %s }"
         (String.concat
            "; "
            (List.map (fun (f, t, _) -> [%string "%{f} = %{literal ctx t}"]) fields))
     | Variant constrs ->
       let c, args = pick ctx constrs in
       construct c (List.map (literal ctx) args)
     | URecord fields ->
       [%string {|#{ %{String.concat "; " (List.map (fun (f, t) -> p "%s = %s" f (literal ctx t)) fields)} }|}])

and construct c = function
  | [] -> c
  | args -> [%string {|(%{c} (%{String.concat ", " args}))|}]
;;

(* [raise Exit] at any type. raise only has value types, so unboxed results are
   built around it. *)
let rec raise_at ctx ty =
  match ty with
  | U UF -> "(unbox_float (raise Exit))"
  | U _ -> convert (boxed_of ty) ty "(raise Exit)"
  | UTuple ts -> [%string {|#(%{String.concat ", " (List.map (raise_at ctx) ts)})|}]
  | Or_null _ -> "(This (raise Exit))"
  | Named i ->
    (match ctx.decls.(i) with
     | URecord fields ->
       [%string {|#{ %{String.concat "; " (List.map (fun (f, t) -> p "%s = %s" f (raise_at ctx t)) fields)} }|}]
     | _ -> "(raise Exit)")
  | _ -> "(raise Exit)"
;;
