open Hegel

(* The choices a test case draws, as the engine sees them, with the spans of
   typed expressions and of top-level bindings. The lift pass edits them. *)

type choice =
  | I of int
  | B of bool
  | F of float

(* Choices are kept in reverse. *)
let choices : choice list ref = ref []
let count = ref 0

(* (start, stop, type) of each expression span *)
let exprs : (int * int * Ty.ty) list ref = ref []

(* (type start, expression start, expression stop, type) of each top-level binding *)
let bindings : (int * int * int * Ty.ty) list ref = ref []

(* Finds the choices that make a top-level binding have a given type. *)
let binding_types : (Ty.ty -> choice list option) ref = ref (fun _ -> None)

(* With a script, draws read it instead of the engine. [Exhausted] gives the
   kind of draw that found it empty. *)
exception Exhausted of [ `Int of int * int | `Bool ]

let script : choice list option ref = ref None

(* With [tolerant] choices, draws take the next one if it fits, clamped to
   range, and otherwise a default, leaving it for the next draw. What they use
   is recorded, so the result replays exactly. *)
let tolerant : choice list option ref = ref None

let take f default =
  match !tolerant with
  | Some (c :: rest) ->
    (match f c with
     | Some v ->
       tolerant := Some rest;
       v
     | None -> default)
  | _ -> default
;;

let reset () =
  choices := [];
  count := 0;
  exprs := [];
  bindings := []
;;

let record c =
  choices := c :: !choices;
  incr count
;;

let next kind =
  match !script with
  | Some (c :: rest) ->
    script := Some rest;
    c
  | Some [] -> raise (Exhausted kind)
  | None -> assert false
;;

let int tc lo hi =
  if Option.is_some !script
  then (
    match next (`Int (lo, hi)) with
    | I v -> v
    | _ -> raise (Exhausted (`Int (lo, hi))))
  else (
    let v =
      if Option.is_some !tolerant
      then
        take
          (function
            | I v -> Some (max lo (min hi v))
            | _ -> None)
          lo
      else draw_silent tc (integers ~min_value:lo ~max_value:hi ())
    in
    record (I v);
    v)
;;

(* An index into a list of length n, drawn as [sampled_from] draws it. *)
let index tc n =
  if Option.is_some !script
  then int tc 0 (n - 1)
  else if Option.is_some !tolerant
  then int tc 0 (n - 1)
  else (
    let v = draw_silent tc (sampled_from (List.init n Fun.id)) in
    record (I v);
    v)
;;

let bool ?p tc =
  if Option.is_some !script
  then (
    match next `Bool with
    | B b -> b
    | _ -> raise (Exhausted `Bool))
  else (
    let v =
      if Option.is_some !tolerant
      then
        take
          (function
            | B b -> Some b
            | _ -> None)
          false
      else draw_silent tc (booleans ?p ())
    in
    record (B v);
    v)
;;

let unbounded tc =
  let v =
    if Option.is_some !tolerant
    then
      take
        (function
          | I v -> Some v
          | _ -> None)
        0
    else draw_silent tc (integers ())
  in
  record (I v);
  v
;;

(* g must not allow NaN or infinities, as the tolerant default is 0. *)
let float tc g =
  let v =
    if Option.is_some !tolerant
    then
      take
        (function
          | F v when Float.is_finite v -> Some v
          | _ -> None)
        0.
    else draw_silent tc g
  in
  record (F v);
  v
;;

(* The shortest script for which [f] returns [target], searching breadth
   first. Bounded ints try their first 16 values. *)
let search f target =
  let queue = Queue.create () in
  Queue.add [] queue;
  let rec go budget =
    if budget = 0 || Queue.is_empty queue
    then None
    else (
      let s = Queue.pop queue in
      script := Some s;
      match f () with
      | t ->
        script := None;
        if t = target then Some s else go (budget - 1)
      | exception Exhausted kind ->
        script := None;
        (match kind with
         | `Bool -> List.iter (fun b -> Queue.add (s @ [ B b ]) queue) [ false; true ]
         | `Int (lo, hi) ->
           for v = lo to min hi (lo + 15) do
             Queue.add (s @ [ I v ]) queue
           done);
        go (budget - 1))
  in
  let r = go 20000 in
  script := None;
  r
;;

(* Failure blobs: base64 of a 0 prefix and the engine's choice encoding. *)
let base64 s =
  let tbl = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/" in
  let b = Buffer.create ((String.length s + 2) / 3 * 4) in
  let n = String.length s in
  let byte i = if i < n then Char.code s.[i] else 0 in
  let i = ref 0 in
  while !i < n do
    let x = (byte !i lsl 16) lor (byte (!i + 1) lsl 8) lor byte (!i + 2) in
    (* 3 bytes give 4 characters; a short last group gives 2 or 3 and padding *)
    let chars = min 4 (n - !i + 1) in
    for k = 0 to 3 do
      Buffer.add_char b (if k < chars then tbl.[(x lsr (18 - (6 * k))) land 63] else '=')
    done;
    i := !i + 3
  done;
  Buffer.contents b
;;

let blob cs =
  let b = Buffer.create 256 in
  Buffer.add_char b '\000';
  Buffer.add_int32_le b (Int32.of_int (List.length cs));
  List.iter
    (function
      | I v ->
        (* two's complement, little-endian, shortest form with a sign bit *)
        let rec len k =
          if k >= 8 || v asr ((8 * k) - 1) = 0 || v asr ((8 * k) - 1) = -1
          then k
          else len (k + 1)
        in
        let k = len 1 in
        Buffer.add_char b '\000';
        Buffer.add_char b '\010';
        Buffer.add_int32_le b (Int32.of_int k);
        for j = 0 to k - 1 do
          Buffer.add_char b (Char.chr ((v asr (8 * j)) land 255))
        done
      | B v ->
        Buffer.add_char b '\001';
        Buffer.add_char b (if v then '\001' else '\000')
      | F v ->
        Buffer.add_char b '\002';
        Buffer.add_int64_le b (Int64.bits_of_float v))
    cs;
  base64 (Buffer.contents b)
;;

(* The smallest test case that failed. *)
type snapshot =
  { cs : choice array
  ; snap_exprs : (int * int * Ty.ty) list
  ; snap_bindings : (int * int * int * Ty.ty) list
  ; snap_types : Ty.ty -> choice list option
  ; size : int (* length of the program *)
  }

let last : snapshot option ref = ref None

let save size =
  if
    match !last with
    | Some s -> size < s.size
    | None -> true
  then
    last
    := Some
         { cs = Array.of_list (List.rev !choices)
         ; snap_exprs = !exprs
         ; snap_bindings = !bindings
         ; snap_types = !binding_types
         ; size
         }
;;

(* Lifting: a top-level binding becomes an expression found inside it, with its
   type choices changed to that expression's type. Smallest results first. *)
let lifts s =
  let n = Array.length s.cs in
  let sub a b = Array.to_list (Array.sub s.cs a (b - a)) in
  let memo = Hashtbl.create 8 in
  let types t =
    match Hashtbl.find_opt memo t with
    | Some r -> r
    | None ->
      let r = s.snap_types t in
      Hashtbl.add memo t r;
      r
  in
  List.concat_map
    (fun (ty_start, start, stop, ty) ->
       List.filter_map
         (fun (a, b, t) ->
            if a > start && b <= stop && t <> ty
            then
              Option.map
                (fun tys -> sub 0 ty_start @ tys @ sub a b @ sub stop n)
                (types t)
            else None)
         s.snap_exprs)
    s.snap_bindings
  |> List.sort_uniq compare
  |> List.sort (fun x y -> compare (List.length x) (List.length y))
  |> List.filteri (fun i _ -> i < 100)
;;
