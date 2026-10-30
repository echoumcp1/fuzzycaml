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
  [%string "%{prefix}%{ctx.next#Int}"]
;;

let int_in ctx lo hi = Trace.int ctx.tc lo hi
let flip ?p ctx = Trace.bool ?p ctx.tc
let pick ctx l = List.nth l (Trace.index ctx.tc (List.length l))
let choose ctx options = pick ctx options ()

(* The declarations with their indices. *)
let indexed_decls ctx = List.mapi (fun i d -> i, d) (Array.to_list ctx.decls)
let p = Printf.sprintf

(* The variables the program does not refer to yet. *)
let unused ctx vars = List.filter (fun (x, _) -> not (Hashtbl.mem ctx.used x)) vars

(* Parenthesises a negative literal. *)
let paren s = if String.length s > 0 && s.[0] = '-' then [%string "(%{s})"] else s

(* Spans with the same name are what the shrinker swaps for one another, so
   expressions are named by their type. *)
let span ?(name = "fuzzycaml.repeat") ?ty ctx f =
  if Option.is_some !Trace.script
  then f ()
  else (
    let label = Generators.Ppx_internal.Labels.from_name name in
    let start = !Trace.count in
    let v =
      draw_silent
        ctx.tc
        (Generators.Ppx_internal.composite_with_label ~label (fun _ -> f ()))
    in
    Option.iter (fun t -> Trace.exprs := (start, !Trace.count, t) :: !Trace.exprs) ty;
    v)
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
