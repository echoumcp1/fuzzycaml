open Config
open Ty
open Ctx
open Env

(* A class and a subclass that overrides a method and calls the parent's, in a
   local module; the object is one or the other. *)
let objects ctx env ty gen =
  let expr = gen.expr in
  let module_ = fresh ctx "M" in
  let field = fresh ctx "v" in
  let step_arg = fresh ctx "n" in
  let parent_result = fresh ctx "s" in
  (* Objects capture only values. *)
  let env =
    { (closure env) with vars = List.filter (fun (_, t) -> not (restricted t)) env.vars }
  in
  let get = expr (bind env field ty) ty in
  let step = expr (bind (bind env field ty) step_arg ty) ty in
  let get2 = expr (bind (bind env field ty) parent_result ty) ty in
  let init = expr env ty in
  let arg = expr env ty in
  let arg2 = expr env ty in
  let use_subclass = expr env Bool in
  let t = show_ty ty in
  [%string
    "(let module %{module_} = struct class c (i : %{t}) = object (self) val mutable \
     %{field} = i method get : %{t} = %{get} method step (%{step_arg} : %{t}) = %{field} \
     <- %{step}; self#get end class d i = object inherit c i as super method! get = let \
     %{parent_result} = super#get in %{get2} end end in let o = if %{use_subclass} then \
     (new %{module_}.d %{init} :> %{module_}.c) else new %{module_}.c %{init} in ignore \
     (o#step %{arg}); o#step %{arg2})"]
;;

let forms ctx env ty gen =
  boost
    (if (not (restricted ty)) && on "objects"
     then [ (fun () -> objects ctx env ty gen) ]
     else [])
;;
