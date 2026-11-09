open Config
open Ty
open Ctx

type params =
  { first_order : bool
  ; unboxed : bool
  ; depth : int
  ; only : ty list option (* only these, numbers *)
  ; boxed : bool (* only lists, options, pairs and declared types *)
  }

let value_types =
  { first_order = false; unboxed = false; depth = 2; only = None; boxed = false }
;;

let all_types = { value_types with unboxed = true }
let first_order_types = { value_types with first_order = true }

type shape =
  | Is of ty
  | Any of params
  | List_of of shape
  | Option_of of shape
  | Pair_of of shape * shape
  | Or_null_of of shape
  | UTuple_of of shape list
  | Arr_of of int (* an array, its element type drawn at this depth *)

type slot =
  | Base of ty
  | Float_u (* [float#] where unboxed types are allowed *)
  | Named_ of int (* one slot per declaration, so a declared type is one choice *)
  | List_
  | Option_
  | Pair_
  | Arr_
  | Arrow_
  | UTuple_
  | Or_null_

let max_decls = 12

let slots =
  Array.of_list
    ([ Base Int
     ; Base Bool
     ; Base Float
     ; Base Float
     ; Base Float
     ; Base Char
     ; Base Int64
     ; Base Str
     ; List_
     ; Option_
     ; Pair_
     ; Arr_
     ; Arrow_
     ]
     @ List.init max_decls (fun i -> Named_ i)
     @ [ Float_u ]
     @ List.map (fun n -> Base (Num n)) boxed_numbers
     @ List.map (fun u -> Base (Unboxed u)) unboxed_numbers
     @ [ UTuple_; Or_null_ ])
;;

let index_of slot =
  let rec go i =
    if i = Array.length slots
    then invalid_arg "Gen_ty.index_of: no slot"
    else if slots.(i) = slot
    then i
    else go (i + 1)
  in
  go 0
;;

let list_slot = index_of List_
let option_slot = index_of Option_
let pair_slot = index_of Pair_
let arr_slot = index_of Arr_
let or_null_slot = index_of Or_null_
let utuple_slot = index_of UTuple_

let slot_of = function
  | Unboxed UFloat -> index_of Float_u
  | (Int | Bool | Float | Char | Int64 | Str | Num _ | Unboxed _) as t ->
    index_of (Base t)
  | Named i -> index_of (Named_ i)
  | List _ -> list_slot
  | Option _ -> option_slot
  | Pair _ -> pair_slot
  | Arr _ -> arr_slot
  | Arrow _ -> index_of Arrow_
  | UTuple _ -> index_of UTuple_
  | Or_null _ -> index_of Or_null_
;;

let named ctx { first_order; unboxed; _ } =
  List.filter
    (fun i ->
       ((not first_order) || not !not_first_order_decls.(i))
       && (unboxed || not !unboxed_record_decls.(i)))
    (List.init (Array.length ctx.decls) Fun.id)
;;

let allowed ctx params =
  let ox f = !ox_mode && on f in
  let named = named ctx params in
  fun i ->
    match slots.(i), params.only with
    | (List_ | Option_ | Pair_), _ when params.boxed -> params.depth > 0
    | Named_ i, _ when params.boxed -> List.mem i named
    | _, _ when params.boxed -> false
    | Base t, Some tys -> List.mem t tys && slot_of t = i
    | Float_u, Some tys -> List.mem unboxed_float tys
    | _, Some _ -> false
    | Base (Int | Bool | Float | Char | Int64), None -> true
    | Base Str, None -> on "strings"
    | Base (Num n), None -> ox "numbers" && ((not params.first_order) || n <> F32)
    | Base (Unboxed _), None -> params.unboxed && ox "numbers"
    | Base _, None -> false
    | Float_u, None -> params.unboxed && !ox_mode
    | Named_ i, None -> List.mem i named
    | (List_ | Option_ | Pair_), None -> params.depth > 0
    | Arr_, None -> (not params.first_order) && params.depth > 0 && on "arrays"
    | Arrow_, None -> params.depth > 0 && not params.first_order
    | UTuple_, None -> params.unboxed && params.depth > 0 && ox "utuples"
    | Or_null_, None -> params.unboxed && params.depth > 0 && ox "or_null"
;;

type elem =
  | Elem of ty
  | Elem_any
  | Elem_float_u
  | Elem_arr
  | Elem_product

let elems =
  Array.of_list
    ([ Elem Int; Elem Float; Elem Int64; Elem Float; Elem_any; Elem_arr; Elem_float_u ]
     @ List.map (fun t -> Elem t) newer_numbers
     @ [ Elem_product ])
;;

(* An unboxed product in an array holds only values the GC scans or only values it
   ignores, so its components come from one of these. *)
let scanned () = [ Int; Bool; Float; Int64 ] @ if on "strings" then [ Str ] else []

let ignored () =
  [ Int; Bool; Char; unboxed_float ]
  @
  if on "numbers"
  then
    [ Unboxed UInt64
    ; Unboxed UInt32
    ; Unboxed UFloat32
    ; Unboxed UInt8
    ; Unboxed UNativeint
    ]
  else []
;;

let array_product ts =
  List.for_all (fun t -> List.mem t (scanned ())) ts
  || List.for_all (fun t -> List.mem t (ignored ())) ts
;;

let product_parts ts = if List.for_all (fun t -> List.mem t (scanned ())) ts then 0 else 1

let elem_allowed depth i =
  match elems.(i) with
  | Elem (Int | Int64) -> true
  | Elem Float -> i < 3 || not !ox_mode
  | Elem_any -> not !ox_mode
  | Elem_arr -> depth > 0
  | Elem_float_u -> !ox_mode && not (on "numbers")
  | Elem_product -> !ox_mode && on "utuples"
  | Elem _ -> !ox_mode && on "numbers"
;;

let elem_of t =
  let rec go i =
    if i >= Array.length elems
    then 4 (* Elem_any *)
    else (
      match elems.(i), t with
      | Elem s, _ when s = t && elem_allowed 1 i -> i
      | Elem_float_u, Unboxed UFloat when elem_allowed 1 i -> i
      | Elem_arr, Arr _ -> i
      | Elem_product, UTuple _ -> i
      | _ -> go (i + 1))
  in
  go 0
;;

let draw_index ctx allowed last_index =
  let rec go () =
    let index = int_in ctx 0 last_index in
    if allowed index then index else go ()
  in
  go ()
;;

let last allowed count =
  let rec go index =
    if index < 0
    then invalid_arg "no slot"
    else if allowed index
    then index
    else go (index - 1)
  in
  go (count - 1)
;;

(* Mostly 2 or 3 components, which shrink to 2, and sometimes wide ones. *)
let utuple_widths =
  Array.init 64 (fun i -> if i < 60 then 2 + (i mod 2) else [| 5; 8; 12; 16 |].(i - 60))
;;

let utuple_width_index n =
  let rec go i = if utuple_widths.(i) = n then i else go (i + 1) in
  go 0
;;

let rec decode ctx params =
  let allowed_slot = allowed ctx params in
  let inner = { params with unboxed = false; boxed = false; depth = params.depth - 1 } in
  let unboxed_inner = { inner with unboxed = true } in
  match slots.(draw_index ctx allowed_slot (last allowed_slot (Array.length slots))) with
  | Base t -> t
  | Float_u -> unboxed_float
  | Named_ i -> Named i
  | List_ -> List (decode ctx inner)
  | Option_ -> Option (decode ctx inner)
  | Pair_ ->
    let first = decode ctx inner in
    Pair (first, decode ctx inner)
  | Arr_ -> Arr (decode_elem ctx (params.depth - 1))
  | Arrow_ ->
    let first = decode ctx unboxed_inner in
    Arrow (first, decode ctx unboxed_inner)
  | UTuple_ ->
    UTuple (List.init utuple_widths.(int_in ctx 0 63) (fun _ -> decode ctx unboxed_inner))
  | Or_null_ -> Or_null (decode ctx inner)

and decode_elem ctx depth =
  let allowed_slot = elem_allowed depth in
  match elems.(draw_index ctx allowed_slot (last allowed_slot (Array.length elems))) with
  | Elem t -> t
  | Elem_any -> decode ctx { value_types with depth }
  | Elem_float_u -> unboxed_float
  | Elem_arr -> Arr (decode_elem ctx (depth - 1))
  | Elem_product ->
    let components = if int_in ctx 0 1 = 0 then scanned () else ignored () in
    UTuple
      (List.init (int_in ctx 2 3) (fun _ ->
         List.nth components (int_in ctx 0 (List.length components - 1))))
;;

let draw_fixed ctx i = ignore (int_in ctx i i)

let rec encode ctx ty =
  draw_fixed ctx (slot_of ty);
  match ty with
  | List inner | Option inner | Or_null inner -> encode ctx inner
  | Pair (first, second) | Arrow (first, second) ->
    encode ctx first;
    encode ctx second
  | UTuple component_tys ->
    draw_fixed ctx (utuple_width_index (List.length component_tys));
    List.iter (encode ctx) component_tys
  | Arr inner -> encode_elem ctx inner
  | Int | Bool | Float | Char | Int64 | Str | Num _ | Unboxed _ | Named _ -> ()

and encode_elem ctx elem_ty =
  let slot = elem_of elem_ty in
  draw_fixed ctx slot;
  match elems.(slot), elem_ty with
  | Elem_any, _ -> encode ctx elem_ty
  | Elem_arr, Arr elem_ty -> encode_elem ctx elem_ty
  | Elem_product, UTuple component_tys ->
    let parts_index = product_parts component_tys in
    let components = if parts_index = 0 then scanned () else ignored () in
    draw_fixed ctx parts_index;
    draw_fixed ctx (List.length component_tys);
    List.iter
      (fun component ->
         draw_fixed ctx (Option.get (List.find_index (( = ) component) components)))
      component_tys
  | _ -> ()
;;

let draw_ty ctx ?(candidates = []) ?(p = 0.85) shape =
  let free =
    match shape with
    | Is _ -> false
    | _ -> true
  in
  if flip ~p:(if free && candidates <> [] then p else 0.) ctx
  then pick ctx candidates
  else (
    let rec draw_shape = function
      | Is ty ->
        encode ctx ty;
        ty
      | Any params -> decode ctx params
      | List_of inner_shape ->
        draw_fixed ctx list_slot;
        List (draw_shape inner_shape)
      | Option_of inner_shape ->
        draw_fixed ctx option_slot;
        Option (draw_shape inner_shape)
      | Pair_of (first, b) ->
        draw_fixed ctx pair_slot;
        let first = draw_shape first in
        Pair (first, draw_shape b)
      | Or_null_of inner_shape ->
        draw_fixed ctx or_null_slot;
        Or_null (draw_shape inner_shape)
      | UTuple_of shapes ->
        draw_fixed ctx utuple_slot;
        draw_fixed ctx (utuple_width_index (List.length shapes));
        UTuple (List.map draw_shape shapes)
      | Arr_of depth ->
        draw_fixed ctx arr_slot;
        Arr (decode_elem ctx depth)
    in
    draw_shape shape)
;;

let value_type ctx = decode ctx value_types
let any_type ctx = decode ctx all_types
let first_order_type ctx = decode ctx first_order_types
