open Config
open Ty
open Ctx
open Gen_ty
open Env

(* A local functor applied to two arguments. *)
let functor_app ctx env ty gen =
  let expr = gen.expr in
  (* Fresh names from "F" would include F32, a module the prelude defines. *)
  let functor_ = fresh ctx "Fn" in
  let first = fresh ctx "M" in
  let second = fresh ctx "M" in
  let param = fresh ctx "p" in
  (* Fresh, so that a nested functor's parameter does not hide this one. *)
  let arg_module = fresh ctx "X" in
  let param_ty, arg = gen.of_shape env (Any value_types) in
  let env = closure env in
  let body = expr (bind (bind env (arg_module ^ ".k") ty) param param_ty) ty in
  let attr = pick ctx [ ""; "[@inline never]"; "[@inline]"; "[@specialise]" ] in
  let first_k = expr env ty in
  let second_k = expr env ty in
  let which = expr env Bool in
  let ty_name = show_ty ty in
  [%string
    "(let module %{functor_} (%{arg_module} : sig val k : %{ty_name} end) = struct \
     let%{attr} g (%{param} : %{param_ty#Ty}) : %{ty_name} = %{body} end in let module \
     %{first} = %{functor_} (struct let k = %{first_k} end) in let module %{second} = \
     %{functor_} (struct let k = %{second_k} end) in (if %{which} then %{first}.g else \
     %{second}.g) %{arg})"]
;;

(* A first-class module chosen at run time and unpacked. *)
let first_class ctx env ty gen =
  let expr = gen.expr in
  let signature = fresh ctx "S" in
  let unpacked = fresh ctx "Y" in
  let param = fresh ctx "p" in
  let param_ty, arg = gen.of_shape env (Any value_types) in
  let env = closure env in
  let instance () =
    let body = expr (bind env param param_ty) ty in
    let k_expr = expr env ty in
    [%string
      "(module struct let k = %{k_expr} let f (%{param} : %{param_ty#Ty}) : %{ty#Ty} = \
       %{body} end : %{signature}.S)"]
  in
  let second = instance () in
  let first = instance () in
  let which = expr env Bool in
  [%string
    "(let module %{signature} = struct module type S = sig val k : %{ty#Ty} val f : \
     %{param_ty#Ty} -> %{ty#Ty} end end in let module %{unpacked} = (val (if %{which} \
     then %{first} else %{second}) : %{signature}.S) in if Sys.opaque_identity false \
     then %{unpacked}.k else %{unpacked}.f %{arg})"]
;;

let forms ctx env ty gen =
  boost
    (if (not (restricted ty)) && on "functors"
     then
       [ (fun () -> functor_app ctx env ty gen); (fun () -> first_class ctx env ty gen) ]
     else [])
;;
