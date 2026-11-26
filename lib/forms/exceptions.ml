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

(* Older OxCaml compilers have no ref of an unboxed value. *)
let savable ctx =
  List.filter_map
    (fun (decl, fields) ->
       match
         List.filter (fun (field : record_field) -> not (restricted field.ty)) fields
       with
       | [] -> None
       | fields -> Some (decl, fields))
    (mutable_records ctx)
;;

(* The record is new and only this form touches it, and the read, the call and
   the uses are sequenced, so the output is still determined. *)
let saved_read ctx env ty gen =
  let expr = gen.expr in
  let decl, fields = pick ctx (savable ctx) in
  let field = pick ctx fields in
  let record = fresh ctx "q" in
  let saved = fresh ctx "sv" in
  let writer = fresh ctx "w" in
  let param = fresh ctx "p" in
  let inner = pure env in
  let read = [%string "%{record}.%{field.name}"] in
  let init = expr inner field.ty in
  let ref_version = [%string "let %{saved} = ref (%{init} : %{field.ty#Ty}) in"] in
  let ref_assign = [%string "%{saved} := %{read}"] in
  let ref_use = "!" ^ saved in
  let declare, assign, after =
    if !ox_mode && flip ctx
    then (
      (* Erased, the [let mutable] is a ref. No closure may capture it. *)
      let use = ox_syntax saved ref_use in
      ( ox_syntax
          [%string "let mutable %{saved} : %{field.ty#Ty} = %{init} in"]
          ref_version
      , ox_syntax [%string "%{saved} <- %{read}"] ref_assign
      , { env with mutables = (use, field.ty) :: env.mutables } ))
    else ref_version, ref_assign, bind env ref_use field.ty
  in
  let after = bind after read field.ty in
  let attr =
    pick ctx [ ""; "[@inline never]"; "[@inline never] [@local never]"; "[@local never]" ]
  in
  let new_value =
    expr (bind inner [%string "%{param}.%{field.name}"] field.ty) field.ty
  in
  let raises =
    if flip ctx then "raise Exit" else [%string "if %{expr inner Bool} then raise Exit"]
  in
  let body = expr { after with in_try = true } ty in
  let handler = expr after ty in
  [%string
    "(let %{record} = %{fresh_record ctx inner gen decl} in %{declare} let%{attr} \
     %{writer} (%{param} : t%{decl#Int}) = %{param}.%{field.name} <- %{new_value}; \
     %{raises} in try %{assign}; %{writer} %{record}; %{body} with Exit -> %{handler})"]
;;

let forms ctx env ty gen =
  let value = not (restricted ty) in
  boost (if value && on "exns" then [ (fun () -> local_exn ctx env ty gen) ] else [])
  @ gate
      (value && on "exns" && savable ctx <> [])
      [ (fun () -> saved_read ctx env ty gen) ]
;;
