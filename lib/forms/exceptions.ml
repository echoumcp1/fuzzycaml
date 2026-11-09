open Config
open Ty
open Ctx
open Gen_ty
open Env

let local_exn ctx env ty gen =
  let expr = gen.expr in
  let exn = fresh ctx "X" in
  let thrower = fresh ctx "th" in
  let should_raise = fresh ctx "b" in
  let payload = fresh ctx "v" in
  let should_raise_arg = fresh ctx "c" in
  let payload_arg = fresh ctx "c" in
  let env = closure env in
  let payload_ty, payload_value =
    gen.of_shape
      ~candidates:(candidates ctx env first_order_ty)
      env
      (Any first_order_types)
  in
  let handler = expr (bind env payload payload_ty) ty in
  let condition = expr env Bool in
  let no_raise = expr (bind (bind env should_raise Bool) payload payload_ty) ty in
  let raise = pick ctx [ "raise"; "raise_notrace" ] in
  let attr = pick ctx [ ""; "[@inline never]" ] in
  [%string
    "(let exception %{exn} of %{payload_ty#Ty} in let%{attr} %{thrower} (%{should_raise} \
     : bool) (%{payload} : %{payload_ty#Ty}) : %{ty#Ty} = if %{should_raise} then \
     %{raise} (%{exn} %{payload}) else %{no_raise} in let %{should_raise_arg} = \
     %{condition} in let %{payload_arg} = %{payload_value} in try %{thrower} \
     %{should_raise_arg} %{payload_arg} with %{exn} %{payload} -> %{handler})"]
;;

let forms ctx env ty gen =
  boost
    (if (not (restricted ty)) && on "exns"
     then [ (fun () -> local_exn ctx env ty gen) ]
     else [])
;;
