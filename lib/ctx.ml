open Hegel
open Ty

type ctx =
  { tc : test_case
  ; mutable next : int
  ; mutable decls : decl array
  ; mutable effects : (string * ty * ty) list
  ; used : (string, unit) Hashtbl.t
  }

let fresh ctx prefix =
  ctx.next <- ctx.next + 1;
  [%string "%{prefix}%{ctx.next#Int}"]
;;

let int_in ctx lo hi = Draw.int ctx.tc lo hi
let flip ?p ctx = Draw.bool ?p ctx.tc
let pick ctx l = List.nth l (int_in ctx 0 (List.length l - 1))

exception Inapplicable

let gate applicable forms =
  if applicable then forms else List.map (fun _ () -> raise Inapplicable) forms
;;

let choose ctx options =
  let rec go n =
    if n = 0 then invalid_arg "choose: no applicable form";
    match pick ctx options () with
    | v -> v
    | exception Inapplicable -> go (n - 1)
  in
  go 10_000
;;

let indexed_decls ctx = List.mapi (fun i d -> i, d) (Array.to_list ctx.decls)

let some ctx n l =
  let flips = List.init (max n (List.length l)) (fun _ -> flip ctx) in
  List.filteri (fun i _ -> List.nth flips i) l
;;

(* OCaml evaluates function arguments and [%string] holes right to left, so draws taken
   out of a template are bound rightmost first, to keep the sequence of choices. *)
let p = Printf.sprintf
let unused ctx vars = List.filter (fun (x, _) -> not (Hashtbl.mem ctx.used x)) vars
let paren s = if String.length s > 0 && s.[0] = '-' then [%string "(%{s})"] else s

(* The [f = v; ...] inside a record expression, with each value drawn by [value]. *)
let field_values value fields =
  String.concat
    "; "
    (List.map (fun (field, field_ty) -> [%string "%{field} = %{value field_ty}"]) fields)
;;

let label = Generators.Ppx_internal.Labels.from_name
let repeat_label = label "fuzzycaml.repeat"
let expr_label = label "fuzzycaml.expr"

let span ?(label = repeat_label) ctx f =
  draw_silent ctx.tc (Generators.Ppx_internal.composite_with_label ~label (fun _ -> f ()))
;;

let repeat ctx lo hi f =
  let rec go i =
    if i >= hi
    then []
    else (
      match
        span ctx (fun () ->
          if flip ~p:(if i < lo then 1. else 0.7) ctx then Some (f i) else None)
      with
      | Some x -> x :: go (i + 1)
      | None -> [])
  in
  go 0
;;
