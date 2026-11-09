open Config
open Ty
open Ctx
open Gen_ty
open Env

let lazy_value ctx env ty gen =
  let expr = gen.expr in
  let values = candidates ctx env (fun t -> if restricted t then None else Some t) in
  let value_ty, body =
    gen.of_shape ~candidates:values (lazy_body env) (Any value_types)
  in
  let lazy_var = fresh ctx "lz" in
  let var = fresh ctx "x" in
  choose
    ctx
    [ (fun () ->
        let force = [%string "(Lazy.force %{lazy_var})"] in
        [%string
          "(let %{lazy_var} = lazy %{body} in %{expr (bind env force value_ty) ty})"])
    ; (fun () ->
        [%string
          "(match lazy %{body} with lazy %{var} -> %{expr (bind env var value_ty) ty})"])
    ; (fun () ->
        [%string "(Lazy.force (Lazy.from_fun (fun () -> %{expr (lazy_body env) ty})))"])
    ]
;;

let forms ctx env ty gen =
  boost
    (if (not (restricted ty)) && on "lazy"
     then [ (fun () -> lazy_value ctx env ty gen) ]
     else [])
;;
