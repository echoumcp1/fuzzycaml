open Hegel
open Ty

type ctx =
  { tc : test_case
  ; mutable next : int
  ; mutable decls : decl array
  ; mutable effects : (string * ty * ty) list (* constructor, argument, result *)
  ; used : (string, unit) Hashtbl.t (* variables the program refers to so far *)
  }

let label = Generators.Ppx_internal.Labels.from_name "fuzzycaml.expr"

let fresh ctx prefix =
  ctx.next <- ctx.next + 1;
  Printf.sprintf "%s%d" prefix ctx.next
;;

let int_in ctx lo hi = draw_silent ctx.tc (integers ~min_value:lo ~max_value:hi ())
let choose ctx options = (List.nth options (int_in ctx 0 (List.length options - 1))) ()
let p = Printf.sprintf

let span ctx f =
  draw_silent ctx.tc (Generators.Ppx_internal.composite_with_label ~label (fun _ -> f ()))
;;

(* Between lo and hi elements. Each one past lo is behind a continue bit and in
   its own span, so the shrinker can delete any one of them. *)
let repeat ctx lo hi f =
  let rec go i =
    if i < hi && (i < lo || draw_silent ctx.tc (booleans ~p:0.7 ()))
    then (
      let x = span ctx (fun () -> f i) in
      x :: go (i + 1))
    else []
  in
  go 0
;;
