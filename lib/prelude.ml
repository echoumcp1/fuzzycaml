open Config

(* NaN's sign is not preserved consistently by constant folding, so all NaNs
   print alike; compare promises only a sign, which flambda folds to the
   difference of chars, so its result goes through sgn. *)
let prelude () =
  {|let show_float f = if Float.is_nan f then "nan" else Printf.sprintf "%h" f
let sdiv a b = if b = 0 then a else a / b
let smod a b = if b = 0 then a else a mod b
let sgn c = if c < 0 then -1 else if c > 0 then 1 else 0
let i64div a b = if b = 0L then a else Int64.div a b
let i64rem a b = if b = 0L then a else Int64.rem a b
let ssub s i n = let l = String.length s in let i = (i land max_int) mod (l + 1) in String.sub s i ((n land max_int) mod (l - i + 1))
let rec take n l = if n <= 0 then [] else match l with [] -> [] | x :: r -> x :: take (n - 1) r
type _ gx =
  | GInt : int -> int gx
  | GBool : bool -> bool gx
  | GAdd : int gx * int gx -> int gx
  | GLe : int gx * int gx -> bool gx
  | GIf : bool gx * 'a gx * 'a gx -> 'a gx
  | GPair : 'a gx * 'b gx -> ('a * 'b) gx
  | GFst : ('a * 'b) gx -> 'a gx
  | GSnd : ('a * 'b) gx -> 'b gx
  | GLit : 'a -> 'a gx
let rec geval : type a. a gx -> a = function
  | GInt n -> n
  | GBool b -> b
  | GAdd (a, b) -> let x = geval a in x + geval b
  | GLe (a, b) -> let x = geval a in x <= geval b
  | GIf (c, a, b) -> if geval c then geval a else geval b
  | GPair (a, b) -> let x = geval a in (x, geval b)
  | GFst q -> fst (geval q)
  | GSnd q -> snd (geval q)
  | GLit v -> v
let gbump : type a. a gx -> a -> a = fun g v ->
  match g with GInt _ -> v + 1 | GBool _ -> not v | GAdd _ -> v - 1 | GLe _ -> v | _ -> v
|}
  ^
  if !ox_mode
  then
    {|external box_float : float# -> (float[@local_opt]) = "%box_float"
external unbox_float : (float[@local_opt]) -> float# = "%unbox_float"
let[@inline always] fu_add x y = unbox_float (box_float x +. box_float y)
let[@inline always] fu_sub x y = unbox_float (box_float x -. box_float y)
let[@inline always] fu_mul x y = unbox_float (Sys.opaque_identity (box_float x *. box_float y))
let[@inline never] fu_div x y = unbox_float (box_float x /. box_float y)
let fu_sqrt x = unbox_float (sqrt (box_float x))
module F32 = Stdlib_stable.Float32
module F32u = Stdlib_stable.Float32_u
module I8 = Stdlib_stable.Int8
module I8u = Stdlib_stable.Int8_u
module I16 = Stdlib_stable.Int16
module I16u = Stdlib_stable.Int16_u
module Iu = Stdlib_stable.Int_u
module Fu = Stdlib_upstream_compatible.Float_u
module I32u = Stdlib_upstream_compatible.Int32_u
module I64u = Stdlib_upstream_compatible.Int64_u
module Natu = Stdlib_upstream_compatible.Nativeint_u
external array_make : ('a : any mod separable). int -> 'a -> 'a array = "%makearray_dynamic" [@@layout_poly]
external array_get : ('a : any mod separable). 'a array -> int -> 'a = "%array_safe_get" [@@layout_poly]
external array_set : ('a : any mod separable). 'a array -> int -> 'a -> unit = "%array_safe_set" [@@layout_poly]
external array_length : ('a : any mod separable). 'a array -> int = "%array_length" [@@layout_poly]
let fsat w f =
  let b = Float.ldexp 1. (w - 1) in
  if Float.is_nan f then 0L
  else if f >= b then (if w = 64 then Int64.max_int else Int64.pred (Int64.shift_left 1L (w - 1)))
  else if f < -. b then (if w = 64 then Int64.min_int else Int64.neg (Int64.shift_left 1L (w - 1)))
  else Int64.of_float f
|}
  else ""
;;
