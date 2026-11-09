open Ty
open Ctx
open Gen_ty
open Env

(* A number of another type, converted to [num_ty]. *)
let converted env t gen () =
  let from_ty, value =
    gen.of_shape
      env
      (Any { value_types with only = Some ([ Int; Int64; Float ] @ newer_numbers) })
  in
  convert from_ty t value
;;

let num_ops ctx env num_ty gen =
  let expr = gen.expr in
  let module_ = num_module num_ty in
  let call fn args () =
    [%string {|(%{module_}.%{fn} %{String.concat " " (List.map (expr env) args)})|}]
  in
  converted env num_ty gen
  ::
  (if is_float num_ty
   then
     [ call "add" [ num_ty; num_ty ]
     ; call "sub" [ num_ty; num_ty ]
     ; call "div" [ num_ty; num_ty ]
     ; call "neg" [ num_ty ]
     ; call "abs" [ num_ty ]
     ; call "sqrt" [ num_ty ] (* Opaque so arm64 cannot fuse the product into an fmadd. *)
     ; (fun () ->
         let boxed = boxed_of num_ty in
         convert
           boxed
           num_ty
           (let product =
              [%string "(%{module_}.mul %{expr env num_ty} %{expr env num_ty})"]
            in
            [%string "(Sys.opaque_identity %{convert num_ty boxed product})"]))
     ]
   else
     List.map
       (fun fn -> call fn [ num_ty; num_ty ])
       [ "add"; "sub"; "mul"; "logand"; "logor"; "logxor" ]
     @ [ call "neg" [ num_ty ]
       ; (fun () ->
           let bit_width = width num_ty in
           let shift = pick ctx [ "shift_left"; "shift_right"; "shift_right_logical" ] in
           let count =
             choose
               ctx
               [ (fun () ->
                   string_of_int (pick ctx [ 0; 1; bit_width - 2; bit_width - 1 ]))
               ; (fun () ->
                   [%string
                     "(%{expr env Int} land %{if bit_width = 63 then 31 else bit_width - \
                      1#Int})"])
               ]
           in
           [%string "(%{module_}.%{shift} %{expr env num_ty} %{count})"])
       ])
;;

let num_compare ctx env gen =
  let num_ty, value =
    gen.of_shape env (Any { value_types with only = Some newer_numbers })
  in
  let common_ty = if is_float num_ty then Float else Int64 in
  let module_ = if is_float num_ty then "Float" else "Int64" in
  let left = convert num_ty common_ty value in
  let right = convert num_ty common_ty (gen.expr env num_ty) in
  choose
    ctx
    [ (fun () -> [%string "(%{module_}.compare %{left} %{right} < 0)"])
    ; (fun () -> [%string "(%{module_}.equal %{left} %{right})"])
    ]
;;
