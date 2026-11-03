open Config
open Ty
open Ctx

(* An expression's span starts with the choices that give its type, so that
   when the shrinker replaces a span with one of its descendants, a position
   that draws its type reads the descendant's, and a position whose type the
   context fixes keeps its own.

   A type is a sequence of indices into [slots], the same at every position. A
   fixed position draws each from a single-value range, so there is nothing to
   shrink; a free position draws from the range up to the last allowed slot
   and draws again on a slot it does not allow. *)

type params =
  { first_order : bool
  ; unboxed : bool
  ; depth : int
  ; only : ty list option (* only these, numbers *)
  ; boxed : bool (* only lists, options, pairs and declared types *)
  }

let any = { first_order = false; unboxed = false; depth = 2; only = None; boxed = false }
let top = { any with unboxed = true }
let fo = { any with first_order = true }

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

(* A program declares up to four types, each with an unboxed twin, and up to
   four more unboxed records. *)
let max_decls = 12

(* The slots allowed without --ox come first, so that those draws have a short
   range. Float has three slots, as it always had three options. *)
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
     @ List.map (fun n -> Base (Num n)) all_nb
     @ List.map (fun u -> Base (U u)) all_ub
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
  | U UF -> index_of Float_u
  | (Int | Bool | Float | Char | Int64 | Str | Num _ | U _) as t -> index_of (Base t)
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
    (fun i -> ((not first_order) || not !mixed.(i)) && (unboxed || not !urec.(i)))
    (List.init (Array.length ctx.decls) Fun.id)
;;

let allowed ctx prm =
  let ox f = !ox_mode && on f in
  let named = named ctx prm in
  fun i ->
    match slots.(i), prm.only with
    | (List_ | Option_ | Pair_), _ when prm.boxed -> prm.depth > 0
    | Named_ i, _ when prm.boxed -> List.mem i named
    | _, _ when prm.boxed -> false
    | Base t, Some tys -> List.mem t tys && slot_of t = i
    | Float_u, Some tys -> List.mem float_u tys
    | _, Some _ -> false
    | Base (Int | Bool | Float | Char | Int64), None -> true
    | Base Str, None -> on "strings"
    | Base (Num n), None -> ox "numbers" && ((not prm.first_order) || n <> F32)
    | Base (U _), None -> prm.unboxed && ox "numbers"
    | Base _, None -> false
    | Float_u, None -> prm.unboxed && !ox_mode
    | Named_ i, None -> List.mem i named
    | (List_ | Option_ | Pair_), None -> prm.depth > 0
    | Arr_, None -> (not prm.first_order) && prm.depth > 0 && on "arrays"
    | Arrow_, None -> prm.depth > 0 && not prm.first_order
    | UTuple_, None -> prm.unboxed && prm.depth > 0 && ox "utuples"
    | Or_null_, None -> prm.unboxed && prm.depth > 0 && ox "or_null"
;;

(* Array elements, with their own slots: floats are more likely, since float
   arrays are stored flat. *)
type elem =
  | Elem of ty
  | Elem_any
  | Elem_float_u
  | Elem_arr

let elems =
  Array.of_list
    ([ Elem Int; Elem Float; Elem Int64; Elem Float; Elem_any; Elem_arr; Elem_float_u ]
     @ List.map (fun t -> Elem t) newer_nums)
;;

let elem_allowed depth i =
  match elems.(i) with
  | Elem (Int | Int64) -> true
  | Elem Float -> i < 3 || not !ox_mode
  | Elem_any -> not !ox_mode
  | Elem_arr -> depth > 0
  | Elem_float_u -> !ox_mode && not (on "numbers")
  | Elem _ -> !ox_mode && on "numbers"
;;

let elem_of t =
  let rec go i =
    if i >= Array.length elems
    then 4 (* Elem_any *)
    else (
      match elems.(i), t with
      | Elem s, _ when s = t && elem_allowed 1 i -> i
      | Elem_float_u, U UF when elem_allowed 1 i -> i
      | Elem_arr, Arr _ -> i
      | _ -> go (i + 1))
  in
  go 0
;;

let draw_index ctx ok last =
  let rec go () =
    let i = int_in ctx 0 last in
    if ok i then i else go ()
  in
  go ()
;;

let last ok n =
  let rec go i =
    if i < 0 then invalid_arg "no slot" else if ok i then i else go (i - 1)
  in
  go (n - 1)
;;

let rec decode ctx prm =
  let ok = allowed ctx prm in
  let sub = { prm with unboxed = false; boxed = false; depth = prm.depth - 1 } in
  let unboxed_sub = { sub with unboxed = true } in
  match slots.(draw_index ctx ok (last ok (Array.length slots))) with
  | Base t -> t
  | Float_u -> float_u
  | Named_ i -> Named i
  | List_ -> List (decode ctx sub)
  | Option_ -> Option (decode ctx sub)
  | Pair_ ->
    let a = decode ctx sub in
    Pair (a, decode ctx sub)
  | Arr_ -> Arr (decode_elem ctx (prm.depth - 1))
  | Arrow_ ->
    let a = decode ctx unboxed_sub in
    Arrow (a, decode ctx unboxed_sub)
  | UTuple_ -> UTuple (List.init (int_in ctx 2 3) (fun _ -> decode ctx unboxed_sub))
  | Or_null_ -> Or_null (decode ctx sub)

and decode_elem ctx depth =
  let ok = elem_allowed depth in
  match elems.(draw_index ctx ok (last ok (Array.length elems))) with
  | Elem t -> t
  | Elem_any -> decode ctx { any with depth }
  | Elem_float_u -> float_u
  | Elem_arr -> Arr (decode_elem ctx (depth - 1))
;;

let fixed ctx i = ignore (int_in ctx i i)

(* the choices [decode] reads as [t] *)
let rec encode ctx t =
  fixed ctx (slot_of t);
  match t with
  | List s | Option s | Or_null s -> encode ctx s
  | Pair (a, b) | Arrow (a, b) ->
    encode ctx a;
    encode ctx b
  | UTuple ts ->
    fixed ctx (List.length ts);
    List.iter (encode ctx) ts
  | Arr s -> encode_elem ctx s
  | Int | Bool | Float | Char | Int64 | Str | Num _ | U _ | Named _ -> ()

and encode_elem ctx s =
  let i = elem_of s in
  fixed ctx i;
  match elems.(i), s with
  | Elem_any, _ -> encode ctx s
  | Elem_arr, Arr s -> encode_elem ctx s
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
    let rec go = function
      | Is t ->
        encode ctx t;
        t
      | Any prm -> decode ctx prm
      | List_of sh ->
        fixed ctx list_slot;
        List (go sh)
      | Option_of sh ->
        fixed ctx option_slot;
        Option (go sh)
      | Pair_of (a, b) ->
        fixed ctx pair_slot;
        let a = go a in
        Pair (a, go b)
      | Or_null_of sh ->
        fixed ctx or_null_slot;
        Or_null (go sh)
      | UTuple_of shapes ->
        fixed ctx utuple_slot;
        fixed ctx (List.length shapes);
        UTuple (List.map go shapes)
      | Arr_of depth ->
        fixed ctx arr_slot;
        Arr (decode_elem ctx depth)
    in
    go shape)
;;

let any_ty ctx = decode ctx any
let top_ty ctx = decode ctx top
let fo_ty ctx = decode ctx fo
