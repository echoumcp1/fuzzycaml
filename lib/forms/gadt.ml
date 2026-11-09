open Config
open Ty
open Ctx
open Gen_ty
open Env

let rec gadt ctx env shape gen depth =
  let expr = gen.expr in
  let smaller sh = gadt ctx env sh gen (depth - 1) in
  let of_type node_ty = snd (smaller (Is node_ty)) in
  let literal_node () =
    let node_ty, first_code = gen.of_shape env shape in
    node_ty, [%string "(GLit %{first_code})"]
  in
  if depth <= 0
  then literal_node ()
  else
    choose
      ctx
      ([ literal_node
       ; (fun () ->
           let condition = of_type Bool in
           let node_ty, first = smaller shape in
           let second = of_type node_ty in
           node_ty, [%string "(GIf (%{condition}, %{first}, %{second}))"])
       ; (fun () ->
           match smaller (Pair_of (shape, Any first_order_types)) with
           | Pair (first, _), pair -> first, [%string "(GFst %{pair})"]
           | _ -> assert false)
       ; (fun () ->
           match smaller (Pair_of (Any first_order_types, shape)) with
           | Pair (_, second), pair -> second, [%string "(GSnd %{pair})"]
           | _ -> assert false)
       ]
       @
       match shape with
       | Is Int ->
         [ (fun () -> Int, [%string "(GInt %{expr env Int})"])
         ; (fun () ->
             let first = of_type Int in
             let second = of_type Int in
             Int, [%string "(GAdd (%{first}, %{second}))"])
         ]
       | Is Bool ->
         [ (fun () -> Bool, [%string "(GBool %{expr env Bool})"])
         ; (fun () ->
             let first = of_type Int in
             let second = of_type Int in
             Bool, [%string "(GLe (%{first}, %{second}))"])
         ]
       | Is (Pair (first, second)) ->
         [ (fun () ->
             let first_code = of_type first in
             let second_code = of_type second in
             Pair (first, second), [%string "(GPair (%{first_code}, %{second_code}))"])
         ]
       | Pair_of (first_shape, second_shape) ->
         [ (fun () ->
             let first, first_code = smaller first_shape in
             let second, second_code = smaller second_shape in
             Pair (first, second), [%string "(GPair (%{first_code}, %{second_code}))"])
         ]
       | _ -> [])
;;

let forms ctx env ty gen =
  let expr = gen.expr in
  boost
    (if first_order ty && on "gadt"
     then
       [ (fun () -> [%string "(geval %{snd (gadt ctx env (Is ty) gen 3)})"])
       ; (fun () ->
           match ty with
           | Int | Bool ->
             [%string "(gbump %{snd (gadt ctx env (Is ty) gen 2)} %{expr env ty})"]
           | _ -> [%string "(geval %{snd (gadt ctx env (Is ty) gen 2)})"])
       ]
     else [])
;;
