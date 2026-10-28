open Ty
open Ctx
open Gen_ty
open Env

(* [let x : t = <e> in ] for each variable. *)
let lets e env vars =
  String.concat "" (List.map (fun (x, t) -> p "let %s : %s = %s in " x (show_ty t) (e env t)) vars)
;;

(* Many ints and floats live across an opaque call, so some must be spilled. *)
let pressure ctx env ty e =
  let n = int_in ctx 8 20 in
  let vars =
    List.init n (fun _ ->
      let t = if flip ctx then Int else Float in
      fresh ctx (if t = Int then "i" else "f"), t)
  in
  let k = fresh ctx "k" in
  let env' = bind_all (bind env k Int) vars in
  let sum t op zero =
    match List.filter (fun (_, t') -> t' = t) vars with
    | [] -> zero
    | xs -> String.concat op (List.map fst xs)
  in
  p
    "(%s let %s = (Sys.opaque_identity succ) %s in if %s = %s || %s > float_of_int %s \
     then %s else %s)"
    (lets e env vars)
    k
    (e env Int)
    (sum Int " + " "0")
    k
    (sum Float " +. " "0.")
    k
    (e env' ty)
    (e env' ty)
;;

(* More int and float parameters than arm64 passes in registers, in a
   function that calls itself in tail position. Arguments are let-bound
   because their evaluation order is unspecified. *)
let many_args ctx env ty e =
  let go = fresh ctx "go" in
  let n = fresh ctx "n" in
  let params =
    List.init (int_in ctx 9 14) (fun _ ->
      ( fresh ctx "a"
      , choose ctx [ (fun () -> Int); (fun () -> Float); (fun () -> fo_ty ctx) ] ))
  in
  let env = closure env in
  let inner = bind_all (bind env n Int) params in
  (* recursive calls mostly pass parameters through, to keep programs small *)
  let arg env t =
    let same = List.filter (fun (_, t') -> t' = t) params in
    if env != inner || same = [] || flip ~p:0.3 ctx
    then e env t
    else fst (pick ctx same)
  in
  let args env first =
    let bound = List.map (fun (_, t) -> fresh ctx "b", t, arg env t) params in
    ( String.concat "" (List.map (fun (y, t, v) -> p "let %s : %s = %s in " y (show_ty t) v) bound)
    , String.concat " " (first :: List.map (fun (y, _, _) -> y) bound) )
  in
  let m = fresh ctx "m" in
  let outer_lets, outer = args env m in
  let inner_lets, again = args inner (p "(%s - 1)" n) in
  p
    "(let%s rec %s (%s : int) %s : %s = if %s <= 0 then %s else (%s%s %s) in let %s = %s \
     land 7 in %s%s %s)"
    (pick ctx [ ""; "[@inline never]" ])
    go
    n
    (String.concat " " (List.map (fun (x, t) -> p "(%s : %s)" x (show_ty t)) params))
    (show_ty ty)
    n
    (e inner ty)
    inner_lets
    go
    again
    m
    (e env Int)
    outer_lets
    (choose ctx [ (fun () -> go); (fun () -> p "(%s [@inlined never])" go) ])
    outer
;;

(* Fresh allocations live across a collection and are used afterwards, so the GC
   must find them wherever the backend keeps them. *)
let gc ctx env ty e =
  let vars = List.init (int_in ctx 2 6) (fun _ -> fresh ctx "g", fo_ty ctx) in
  p
    "(%s%s; %s)"
    (lets e env vars)
    (pick ctx [ "Gc.minor ()"; "Gc.minor ()"; "Gc.full_major ()"; "Gc.compact ()" ])
    (e (bind_all env vars) ty)
;;

(* A string read at an offset inside the string's padding. *)
let str_load ctx env e ty =
  let s = fresh ctx "s" in
  let off = p "((%s land max_int) mod (String.length %s + 1))" (e env Int) s in
  let padded = p "(%s ^ \"\\001\\002\\003\\004\\005\\006\\007\\008\")" s in
  let load =
    match ty with
    | Int ->
      choose
        ctx
        [ (fun () -> p "String.get_uint8 %s %s" padded off)
        ; (fun () -> p "String.get_int8 %s %s" padded off)
        ; (fun () -> p "String.get_int16_le %s %s" padded off)
        ; (fun () -> p "String.get_uint16_be %s %s" padded off)
        ; (fun () -> p "Int32.to_int (String.get_int32_le %s %s)" padded off)
        ; (fun () -> p "Int32.to_int (String.get_int32_be %s %s)" padded off)
        ; (fun () ->
            p
              "(if String.length %s = 0 then 0 else Char.code (String.unsafe_get %s ((%s \
               land max_int) mod String.length %s)))"
              s
              s
              (e env Int)
              s)
        ]
    | Int64 ->
      choose
        ctx
        [ (fun () -> p "String.get_int64_le %s %s" padded off)
        ; (fun () -> p "String.get_int64_be %s %s" padded off)
        ]
    | _ ->
      choose
        ctx
        [ (fun () -> p "%s.[%s]" padded off)
        ; (fun () -> p "String.unsafe_get %s %s" padded off)
        ]
  in
  p "(let %s = %s in %s)" s (e env Str) load
;;

(* A match on literals that share prefixes around the 8-byte word, for the
   compiler's string-match code. *)
let str_match ctx env ty e =
  let letter () = Char.chr (int_in ctx (Char.code 'a') (Char.code 'c')) in
  let base = String.init (int_in ctx 5 10) (fun _ -> letter ()) in
  let n = String.length base in
  let variant () =
    choose
      ctx
      [ (fun () -> base)
      ; (fun () -> String.sub base 0 (int_in ctx 0 n))
      ; (fun () -> base ^ String.init (int_in ctx 1 3) (fun _ -> letter ()))
      ; (fun () -> String.sub base 0 (n - 1) ^ "z")
      ]
  in
  let lits = List.sort_uniq compare (List.init (int_in ctx 1 5) (fun _ -> variant ())) in
  let s =
    choose
      ctx
      [ (fun () -> e env Str)
      ; (fun () -> p "%S" (variant ()))
      ; (fun () -> p "(%S ^ %s)" (String.sub base 0 (int_in ctx 0 n)) (e env Str))
      ]
  in
  p
    "(match %s with %s | _ -> %s)"
    s
    (String.concat " " (List.map (fun l -> p "| %S -> %s" l (e env ty)) lits))
    (e env ty)
;;
