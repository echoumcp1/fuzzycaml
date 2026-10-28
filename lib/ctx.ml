open Hegel
open Ty

type ctx =
  { tc : test_case
  ; mutable next : int
  ; mutable decls : decl array
  ; mutable effects : (string * ty * ty) list (* constructor, argument, result *)
  ; used : (string, unit) Hashtbl.t (* variables the program refers to so far *)
  }

let fresh ctx prefix =
  ctx.next <- ctx.next + 1;
  Printf.sprintf "%s%d" prefix ctx.next
;;

let int_in ctx lo hi = draw_silent ctx.tc (integers ~min_value:lo ~max_value:hi ())
let flip ?p ctx = draw_silent ctx.tc (booleans ?p ())
let pick ctx l = List.nth l (int_in ctx 0 (List.length l - 1))
let choose ctx options = pick ctx options ()

(* The declarations with their indices. *)
let indexed_decls ctx = List.mapi (fun i d -> i, d) (Array.to_list ctx.decls)
let p = Printf.sprintf

(* The variables the program does not refer to yet. *)
let unused ctx vars = List.filter (fun (x, _) -> not (Hashtbl.mem ctx.used x)) vars

(* Parenthesises a negative literal. *)
let paren s = if String.length s > 0 && s.[0] = '-' then p "(%s)" s else s

(* Spans with the same name are what the shrinker swaps for one another, so
   expressions are named by their type. *)
let span ?(name = "fuzzycaml.repeat") ctx f =
  let label = Generators.Ppx_internal.Labels.from_name name in
  draw_silent ctx.tc (Generators.Ppx_internal.composite_with_label ~label (fun _ -> f ()))
;;

(* Between lo and hi elements. Each one past lo is behind a continue bit and in
   its own span, so the shrinker can delete any one of them. *)
let repeat ctx lo hi f =
  let rec go i =
    if i < hi && (i < lo || flip ~p:0.7 ctx)
    then (
      let x = span ctx (fun () -> f i) in
      x :: go (i + 1))
    else []
  in
  go 0
;;
