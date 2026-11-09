(* 128-bit vectors on arm64. Each vector type is a module with the same
   interface in both versions: NEON builtins in the original, and arrays of
   lanes with the same lane-wise semantics in the erased version. *)

type vector =
  | I8
  | I16
  | I32
  | I64
  | F32
  | F64

let all = [ I8; I16; I32; I64; F32; F64 ]

let native = function
  | I8 -> "int8x16"
  | I16 -> "int16x8"
  | I32 -> "int32x4"
  | I64 -> "int64x2"
  | F32 -> "float32x4"
  | F64 -> "float64x2"
;;

let name vector = String.capitalize_ascii (native vector)

let lanes = function
  | I8 -> 16
  | I16 -> 8
  | I32 | F32 -> 4
  | I64 | F64 -> 2
;;

let width vector = 128 / lanes vector

(* The type of a lane outside the vector. *)
let lane = function
  | I8 | I16 | I32 -> Ty.Int
  | I64 -> Ty.Int64
  | F32 | F64 -> Ty.Float
;;

type shape =
  | Unary
  | Binary
  | Shift
  | From_one of vector
  | From_two of vector * vector

(* Each op: its name, shape, NEON builtin and lane-wise definition. In the
   definitions, [w] wraps to the lane width, [u] reads a lane as unsigned, and
   [on_] and [z_] are a lane of ones and of zeros. *)
let ops vector =
  let native_name = native vector in
  let builtin_name op = "caml_neon_" ^ native_name ^ "_" ^ op in
  let lanewise lane_fn = [%string "Array.map (fun x -> %{lane_fn})"] in
  let lanewise2 lane_fn = [%string "Array.map2 (fun x y -> %{lane_fn})"] in
  let ints =
    [ "add", Binary, builtin_name "add", lanewise2 "w (x + y)"
    ; "sub", Binary, builtin_name "sub", lanewise2 "w (x - y)"
    ; "neg", Unary, builtin_name "neg", lanewise "w (- x)"
    ; "cmpeq", Binary, builtin_name "cmpeq", lanewise2 "if x = y then on_ else z_"
    ; "cmpgt", Binary, builtin_name "cmpgt", lanewise2 "if x > y then on_ else z_"
    ; "cmpeqz", Unary, builtin_name "cmpeqz", lanewise "if x = z_ then on_ else z_"
    ; "cmpgez", Unary, builtin_name "cmpgez", lanewise "if x >= z_ then on_ else z_"
    ; "cmpgtz", Unary, builtin_name "cmpgtz", lanewise "if x > z_ then on_ else z_"
    ; "cmplez", Unary, builtin_name "cmplez", lanewise "if x <= z_ then on_ else z_"
    ; "cmpltz", Unary, builtin_name "cmpltz", lanewise "if x < z_ then on_ else z_"
    ; "slli", Shift, builtin_name "slli", "fun k -> " ^ lanewise "w (x lsl k)"
    ; "srli", Shift, builtin_name "srli", "fun k -> " ^ lanewise "w (u x lsr k)"
    ; "srai", Shift, builtin_name "srai", "fun k -> " ^ lanewise "x asr k"
    ; "dup", Unary, builtin_name "dup", "fun a -> Array.map (fun _ -> a.(0)) a"
    ; "band", Binary, builtin_name "bitwise_and", lanewise2 "x land y"
    ; "bor", Binary, builtin_name "bitwise_or", lanewise2 "x lor y"
    ; "bxor", Binary, builtin_name "bitwise_xor", lanewise2 "x lxor y"
    ]
  in
  let sat =
    [ "add_sat", Binary, builtin_name "add_saturating", lanewise2 "sat (x + y)"
    ; "sub_sat", Binary, builtin_name "sub_saturating", lanewise2 "sat (x - y)"
    ; ( "add_satu"
      , Binary
      , builtin_name "add_saturating_unsigned"
      , lanewise2 "w (satu (u x + u y))" )
    ; ( "sub_satu"
      , Binary
      , builtin_name "sub_saturating_unsigned"
      , lanewise2 "w (satu (u x - u y))" )
    ]
  in
  let minmax =
    [ "max", Binary, builtin_name "max", lanewise2 "max x y"
    ; "min", Binary, builtin_name "min", lanewise2 "min x y"
    ; "maxu", Binary, builtin_name "max_unsigned", lanewise2 "if u x >= u y then x else y"
    ; "minu", Binary, builtin_name "min_unsigned", lanewise2 "if u x <= u y then x else y"
    ; "abs", Unary, builtin_name "abs", lanewise "w (abs x)"
    ]
  in
  let widen src =
    let source_name = native src in
    let mask = (1 lsl width src) - 1 in
    [ ( "cvtsx"
      , From_one src
      , [%string "caml_neon_cvtsx_%{source_name}_to_%{native_name}"]
      , "fun a -> Array.init (Array.length a / 2) (fun i -> w a.(i))" )
    ; ( "cvtzx"
      , From_one src
      , [%string "caml_neon_cvtzx_%{source_name}_to_%{native_name}"]
      , [%string
          "fun a -> Array.init (Array.length a / 2) (fun i -> w (a.(i) land %{mask#Int}))"]
      )
    ]
  in
  (* The low half of the result narrows the source; the high half is zero, or
     the low half of another vector of the result type for the high ops. *)
  let narrow src =
    let source_name = native src in
    let convert = [%string "caml_neon_cvt_%{source_name}_to_%{native_name}"] in
    let wrap, saturate = if src = I64 then "w64", "sat64" else "w", "sat" in
    (* The unsigned narrows read their source lanes as unsigned too. *)
    let saturate_unsigned =
      [%string "(fun x -> w (satu (x land %{(1 lsl width src) - 1#Int})))"]
    in
    let low lane_fn =
      [%string
        "fun a -> let h = Array.length a in Array.init (2 * h) (fun i -> if i < h then \
         %{lane_fn} a.(i) else 0)"]
    in
    let high lane_fn =
      [%string
        "fun d a -> let h = Array.length a in Array.init (2 * h) (fun i -> if i < h then \
         d.(i) else %{lane_fn} a.(i - h))"]
    in
    [ "narrow_sat", From_one src, convert ^ "_low_saturating", low saturate
    ; ( "narrow_high_sat"
      , From_two (vector, src)
      , convert ^ "_high_saturating"
      , high saturate )
    ]
    @
    if src = I64
    then [ "narrow", From_one src, convert, low wrap ]
    else
      [ "narrow", From_one src, convert ^ "_low", low wrap
      ; "narrow_high", From_two (vector, src), convert ^ "_high", high wrap
      ; ( "narrow_satu"
        , From_one src
        , convert ^ "_low_saturating_unsigned"
        , low saturate_unsigned )
      ; ( "narrow_high_satu"
        , From_two (vector, src)
        , convert ^ "_high_saturating_unsigned"
        , high saturate_unsigned )
      ]
  in
  let floats =
    let round = if vector = F32 then "r32" else "" in
    [ "add", Binary, builtin_name "add", lanewise2 [%string "%{round} (x +. y)"]
    ; "sub", Binary, builtin_name "sub", lanewise2 [%string "%{round} (x -. y)"]
    ; "mul", Binary, builtin_name "mul", lanewise2 [%string "%{round} (x *. y)"]
    ; "div", Binary, builtin_name "div", lanewise2 [%string "%{round} (x /. y)"]
    ; "max", Binary, builtin_name "max", lanewise2 "Float.max x y"
    ; "min", Binary, builtin_name "min", lanewise2 "Float.min x y"
    ; "sqrt", Unary, builtin_name "sqrt", lanewise [%string "%{round} (sqrt x)"]
    ; "round_near", Unary, builtin_name "round_near", lanewise "rne x"
    ; ( "round_down"
      , Unary
      , builtin_name "round_neg_inf"
      , lanewise "Float.copy_sign (floor x) x" )
    ; ( "round_up"
      , Unary
      , builtin_name "round_pos_inf"
      , lanewise "Float.copy_sign (ceil x) x" )
    ; ( "round_zero"
      , Unary
      , builtin_name "round_towards_zero"
      , lanewise "Float.copy_sign (Float.trunc x) x" )
    ]
  in
  let fcmp src =
    let source_name = native src in
    List.map
      (fun (op, convert) ->
         ( "f" ^ op
         , From_two (src, src)
         , [%string "caml_neon_%{source_name}_%{op}"]
         , lanewise2 [%string "if x %{convert} y then on_ else z_"] ))
      [ "cmeq", "="; "cmge", ">="; "cmgt", ">"; "cmle", "<="; "cmlt", "<" ]
  in
  let without names = List.filter (fun (op, _, _, _) -> not (List.mem op names)) in
  match vector with
  | I8 -> ints @ sat @ minmax @ narrow I16
  | I16 ->
    without [ "band"; "bor"; "bxor" ] ints
    @ sat
    @ minmax
    @ [ "mul", Binary, builtin_name "mul_low", lanewise2 "w (x * y)" ]
    @ widen I8
    @ narrow I32
  | I32 ->
    ints
    @ minmax
    @ [ "mul", Binary, builtin_name "mul_low", lanewise2 "w (x * y)"
      ; "bnot", Unary, builtin_name "bitwise_not", lanewise "lnot x"
      ; ( "cvtt"
        , From_one F32
        , "caml_neon_cvtt_float32x4_to_int32x4"
        , lanewise "Int64.to_int (fsat 32 x)" )
      ]
    @ widen I16
    @ narrow I64
    @ fcmp F32
  | I64 ->
    ints
    @ [ "bnot", Unary, builtin_name "bitwise_not", lanewise "lnot x"
      ; "cvtt", From_one F64, "caml_neon_cvtt_float64x2_to_int64x2", lanewise "fsat 64 x"
      ; ( "cvtsx"
        , From_one I32
        , "caml_neon_cvtsx_int32x4_to_int64x2"
        , "fun a -> Array.init 2 (fun i -> Int64.of_int a.(i))" )
      ; ( "cvtzx"
        , From_one I32
        , "caml_neon_cvtzx_int32x4_to_int64x2"
        , "fun a -> Array.init 2 (fun i -> Int64.of_int (Stdlib.( land ) a.(i) \
           0xffffffff))" )
      ]
    @ fcmp F64
  | F32 ->
    floats
    @ [ ( "cvt"
        , From_one I32
        , "caml_neon_cvt_int32x4_to_float32x4"
        , lanewise "r32 (float_of_int x)" )
      ; ( "of_f64"
        , From_one F64
        , "caml_neon_cvt_float64x2_to_float32x2"
        , "fun a -> Array.init 4 (fun i -> if i < 2 then r32 a.(i) else 0.)" )
      ]
  | F64 ->
    floats
    @ [ ( "cvt"
        , From_one I64
        , "caml_neon_cvt_int64x2_to_float64x2"
        , lanewise "Int64.to_float x" )
      ; ( "of_f32"
        , From_one F32
        , "caml_neon_cvt_float32x2_to_float64x2"
        , "fun a -> Array.init 2 (fun i -> a.(i))" )
      ]
;;

(* The integer vector whose lanes carry a vector's lanes in and out. *)
let carrier = function
  | F32 -> I32
  | F64 -> I64
  | vector -> vector
;;

let builtin = {|= "caml_vec128_unreachable" "|}
let unboxed = {|" [@@noalloc] [@@unboxed] [@@builtin]|}
let untagged = {|" [@@noalloc] [@@builtin]|}

let signature ~erase vector (_, shape, _, _) =
  let ty vector =
    if erase then Ty.to_string (lane vector) ^ " array" else native vector
  in
  let vector_ty = ty vector in
  match shape with
  | Unary -> [%string "%{vector_ty} -> %{vector_ty}"]
  | Binary -> [%string "%{vector_ty} -> %{vector_ty} -> %{vector_ty}"]
  | Shift when erase -> [%string "int -> %{vector_ty} -> %{vector_ty}"]
  | Shift ->
    [%string "(int[@untagged]) -> (%{vector_ty}[@unboxed]) -> (%{vector_ty}[@unboxed])"]
  | From_one first -> [%string "%{ty first} -> %{vector_ty}"]
  | From_two (first, second) -> [%string "%{ty first} -> %{ty second} -> %{vector_ty}"]
;;

let ox_module vector =
  let lane_count = lanes vector in
  let carrier_vector = carrier vector in
  let carrier_name = native carrier_vector in
  let lane_param, lane_in, lane_out =
    match vector with
    | I8 -> "(int[@untagged])", "", "w8"
    | I16 -> "(int[@untagged])", "", "w16"
    | I32 -> "(int32[@unboxed])", "Int32.of_int", "Int32.to_int"
    | I64 -> "(int64[@unboxed])", "", ""
    | F32 -> "(int32[@unboxed])", "Int32.bits_of_float", "vnan (Int32.float_of_bits"
    | F64 -> "(int64[@unboxed])", "Int64.bits_of_float", "vnan (Int64.float_of_bits"
  in
  let close = if vector = F32 || vector = F64 then ")" else "" in
  let cast a b = [%string "external %{a} : %{b} %{builtin}caml_vec128_cast%{unboxed}"] in
  let inserts =
    List.init lane_count (fun i ->
      [%string "let v = insert %{i#Int} v (%{lane_in} (f %{i#Int})) in "])
  in
  let extracts =
    List.init lane_count (fun i ->
      [%string "| %{i#Int} -> %{lane_out} (extract %{i#Int} v)%{close} "])
  in
  let carriers =
    if carrier_vector = vector
    then "let of_c (v : t) = v let to_c (v : t) = v\n"
    else
      cast "of_c" [%string "%{carrier_name} -> t"]
      ^ "\n"
      ^ cast "to_c" [%string "t -> %{carrier_name}"]
      ^ "\n"
  in
  let ops =
    List.map
      (fun ((op, shape, builtin_name, _) as op_info) ->
         let tail = if shape = Shift then untagged else unboxed in
         [%string
           "external %{op} : %{signature ~erase:false vector op_info} \
            %{builtin}%{builtin_name}%{tail}\n"])
      (ops vector)
  in
  [%string
    "module %{name vector} = struct\n\
     type t = %{native vector}\n\
     %{carriers}%{cast \"c_of64\" (\"int64x2 -> \" ^ carrier_name)}\n\
     external zero : int64 -> int64x2 %{builtin}caml_int64x2_low_of_int64%{unboxed}\n\
     external insert : (int[@untagged]) -> (%{carrier_name}[@unboxed]) -> %{lane_param} \
     -> (%{carrier_name}[@unboxed]) %{builtin}caml_neon_%{carrier_name}_insert%{untagged}\n\
     external extract : (int[@untagged]) -> (%{carrier_name}[@unboxed]) -> %{lane_param} \
     %{builtin}caml_neon_%{carrier_name}_extract%{untagged}\n\
     let init f = let v = c_of64 (zero 0L) in %{String.concat \"\" inserts}of_c v\n\
     let get v i = let v = to_c v in match i land %{lane_count - 1#Int} with \
     %{String.concat \"\" extracts}| _ -> assert false\n\
     let[@inline never] opaque (v : t) = v\n\
     %{String.concat \"\" ops}end\n"]
;;

let erased_module vector =
  let lane_count = lanes vector in
  let lane_ty = Ty.to_string (lane vector) in
  let helpers =
    match vector with
    | I8 | I16 | I32 ->
      let lane_width = width vector in
      [%string
        "let w x = let h = 1 lsl %{lane_width - 1#Int} in ((x + h) land (2 * h - 1)) - h\n\
         let u x = x land ((1 lsl %{lane_width#Int}) - 1)\n\
         let sat x = let h = 1 lsl %{lane_width - 1#Int} in max (- h) (min (h - 1) x)\n\
         let satu x = max 0 (min ((1 lsl %{lane_width#Int}) - 1) x)\n\
         let on_ = -1 let z_ = 0\n\
         let w64 x = w (Int64.to_int x)\n\
         let sat64 x = Int64.to_int (max (-0x80000000L) (min 0x7fffffffL x))\n"]
    | I64 ->
      "let w x = x let u x = x let on_ = -1L let z_ = 0L\n\
       let ( + ) = Int64.add let ( - ) = Int64.sub let ( ~- ) = Int64.neg let abs = \
       Int64.abs\n\
       let ( lsl ) = Int64.shift_left let ( lsr ) = Int64.shift_right_logical let ( asr \
       ) = Int64.shift_right\n\
       let ( land ) = Int64.logand let ( lor ) = Int64.logor let ( lxor ) = Int64.logxor \
       let lnot = Int64.lognot\n"
    | F32 -> "let w = r32\n"
    | F64 -> "let w x = x\n"
  in
  let get =
    if vector = F32 || vector = F64
    then "vnan (v.(Stdlib.( land ) i "
    else "(v.(Stdlib.( land ) i "
  in
  (* Annotated, as an op no program uses would keep a weak type. *)
  let ops =
    List.map
      (fun ((op, _, _, def) as op_info) ->
         [%string "let %{op} : %{signature ~erase:true vector op_info} = %{def}\n"])
      (ops vector)
  in
  [%string
    "module %{name vector} = struct\n\
     type t = %{lane_ty} array\n\
     %{helpers}let init f : t = Array.init %{lane_count#Int} (fun i -> w (f i))\n\
     let get (v : t) i = %{get}%{lane_count - 1#Int}))\n\
     let[@inline never] opaque (v : t) = v\n\
     %{String.concat \"\" ops}end\n"]
;;

let common =
  {|let vnan x = if Float.is_nan x then Float.nan else x
let w8 x = ((x + 128) land 255) - 128
let w16 x = ((x + 32768) land 65535) - 32768
let r32 x = Int32.float_of_bits (Int32.bits_of_float x)
let rne x =
  let f = floor x in
  let d = x -. f in
  Float.copy_sign (if d < 0.5 then f else if d > 0.5 then f +. 1. else if Float.rem f 2. = 0. then f else f +. 1.) x
|}
;;

let prelude ~erase =
  common ^ String.concat "" (List.map (if erase then erased_module else ox_module) all)
;;

(* The builtins' symbols, which the linker needs although the code never calls
   them. *)
let symbols () =
  [ "caml_vec128_cast"; "caml_int64x2_low_of_int64" ]
  @ List.concat_map
      (fun vector ->
         let name = native vector in
         [ "caml_neon_" ^ name ^ "_insert"; "caml_neon_" ^ name ^ "_extract" ]
         @ List.map (fun (_, _, nat, _) -> nat) (ops vector))
      [ I8; I16; I32; I64 ]
  @ List.concat_map
      (fun vector -> List.map (fun (_, _, nat, _) -> nat) (ops vector))
      [ F32; F64 ]
  |> List.sort_uniq compare
;;
