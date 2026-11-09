open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Env

(* The body's type is immediate, so no local escapes. *)
let local_binding ctx env ty gen =
  let expr = gen.expr in
  let bound = fresh ctx "l" in
  let boxed_types = { value_types with boxed = true } in
  let allocation bound_ty env =
    match bound_ty with
    | Pair (a, b) -> Some (fun () -> [%string "(%{expr env a}, %{expr env b})"])
    | List elem_ty ->
      Some (fun () -> [%string "(%{expr env elem_ty} :: %{expr env bound_ty})"])
    | Option elem_ty -> Some (fun () -> [%string "(Some %{expr env elem_ty})"])
    | Named i ->
      (match ctx.decls.(i) with
       | Record fields ->
         Some (fun () -> [%string "{ %{field_values (expr env) (field_types fields)} }"])
       | Variant constrs ->
         (match List.filter (fun (_, args) -> args <> []) constrs with
          | [] -> None
          | constrs ->
            Some
              (fun () ->
                let constructor, args = pick ctx constrs in
                construct constructor (List.map (expr env) args)))
       | URecord _ -> None)
    | _ -> None
  in
  let make = fresh ctx "mk" in
  let param = fresh ctx "z" in
  let bound_ty, source =
    choose
      ctx
      [ (fun () -> gen.of_shape env (Any boxed_types))
      ; (fun () ->
          let bound_ty = decode ctx boxed_types in
          ( bound_ty
          , match allocation bound_ty env with
            | Some build -> ox_syntax "stack_ " "" ^ build ()
            | None -> expr env bound_ty ))
      ; (fun () ->
          let bound_ty = decode ctx boxed_types in
          ( bound_ty
          , match allocation bound_ty (bind (closure env) param Int) with
            | Some build ->
              let local = ox_syntax "exclave_ (stack_ " "(" in
              [%string
                "(let[@inline never] %{make} (%{param} : int) = %{local}%{build ()}) in \
                 %{make} %{expr env Int})"]
            | None -> expr env bound_ty ))
      ]
  in
  let local = ox_syntax "local_ " "" in
  [%string
    "(let %{local}%{bound} : %{bound_ty#Ty} = %{source} in %{expr (bind_local env bound \
     bound_ty) ty})"]
;;

let forms ctx env ty gen =
  if !ox_mode && immediate ty && on "locals"
  then [ (fun () -> local_binding ctx env ty gen) ]
  else []
;;
