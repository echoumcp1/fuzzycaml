open Config
open Ty
open Ctx
open Env

(* A bigarray of a kind that reads back as [ty]. Sizes and indices are bound before
   they are used, and indices are in bounds, except in a store that catches the
   error. *)
let bigarray ctx env ty gen =
  let expr = gen.expr in
  let kind =
    pick
      ctx
      (match ty with
       | Int ->
         [ "int"; "int8_signed"; "int8_unsigned"; "int16_signed"; "int16_unsigned" ]
       | Float -> [ "float64"; "float32" ]
       | Int64 -> [ "int64" ]
       | Num I32 -> [ "int32" ]
       | Num Nat -> [ "nativeint" ]
       | Char -> [ "char" ]
       | _ -> invalid_arg "bigarray")
  in
  let fortran = flip ctx in
  let first_index = if fortran then 1 else 0 in
  let layout = if fortran then "fortran_layout" else "c_layout" in
  let kind = [%string "Bigarray.%{kind} Bigarray.%{layout}"] in
  let commas = String.concat ", " in
  let spaces = String.concat " " in
  let two_dims = flip ctx in
  let module_ = if two_dims then "Bigarray.Array2" else "Bigarray.Array1" in
  let array = fresh ctx "ba" in
  let size_vars = List.init (if two_dims then 2 else 1) (fun _ -> fresh ctx "n") in
  let size_lets =
    String.concat
      ""
      (List.map
         (fun size_var -> [%string "let %{size_var} = 1 + (%{expr env Int} land 7) in "])
         size_vars)
  in
  let init_params = List.map (fun _ -> fresh ctx "i") size_vars in
  let init =
    expr
      (List.fold_left (fun env param -> bind env param Int) (closure env) init_params)
      ty
  in
  let init_param_decls =
    String.concat " " (List.map (fun param -> [%string "(%{param} : int)"]) init_params)
  in
  let index () =
    let indices = List.map (fun _ -> fresh ctx "k") size_vars in
    ( String.concat
        ""
        (List.map2
           (fun flat_index size_var ->
              [%string
                "let %{flat_index} = %{first_index#Int} + ((%{expr env Int} land \
                 max_int) mod %{size_var}) in "])
           indices
           size_vars)
    , indices )
  in
  let read a =
    let index_lets, indices = index () in
    [%string "%{index_lets}%{a}.{%{commas indices}}"]
  in
  let body =
    choose
      ctx
      ([ (fun () -> read array)
       ; (fun () ->
           let index_lets, indices = index () in
           [%string
             "%{index_lets}%{array}.{%{commas indices}} <- %{expr env ty}; %{read array}"])
       ; (fun () ->
           let indices = List.map (fun _ -> fresh ctx "k") size_vars in
           let index_lets =
             String.concat
               ""
               (List.map2
                  (fun index size_var ->
                     [%string
                       "let %{index} = %{first_index - 1#Int} + ((%{expr env Int} land \
                        max_int) mod (%{size_var} + 2)) in "])
                  indices
                  size_vars)
           in
           [%string
             "%{index_lets}(try %{array}.{%{commas indices}} <- %{expr env ty} with \
              Invalid_argument _ -> ()); %{read array}"])
       ; (fun () ->
           let index_lets, indices = index () in
           [%string "%{index_lets}%{module_}.unsafe_get %{array} %{spaces indices}"])
       ; (fun () ->
           let loop_vars = List.map (fun _ -> fresh ctx "l") size_vars in
           let cell = [%string "%{array}.{%{commas loop_vars}}"] in
           let loop_env =
             bind (List.fold_left (fun env var -> bind env var Int) env loop_vars) cell ty
           in
           let set = [%string "%{cell} <- %{expr loop_env ty}"] in
           let loops =
             List.fold_right2
               (fun var size_var inner ->
                  [%string
                    "for %{var} = %{first_index#Int} to %{size_var} - 1 + \
                     %{first_index#Int} do %{inner} done"])
               loop_vars
               size_vars
               set
           in
           [%string "%{loops}; %{read array}"])
       ; (fun () ->
           let copy = fresh ctx "ba" in
           [%string
             "let %{copy} = %{module_}.create %{kind} %{spaces size_vars} in \
              %{module_}.blit %{array} %{copy}; %{read copy}"])
       ]
       @
       if two_dims
       then
         [ (fun () ->
             let flat_index = fresh ctx "k" in
             let total_size = String.concat " * " size_vars in
             [%string
               "let %{flat_index} = %{first_index#Int} + ((%{expr env Int} land max_int) \
                mod (%{total_size})) in (Bigarray.reshape_1 (Bigarray.genarray_of_array2 \
                %{array}) (%{total_size})).{%{flat_index}}"])
         ]
       else
         [ (fun () ->
             let offset = fresh ctx "o" in
             let var = fresh ctx "l" in
             let size_var = List.hd size_vars in
             [%string
               "let %{offset} = (%{expr env Int} land max_int) mod %{size_var} in let \
                %{var} = (%{expr env Int} land max_int) mod (%{size_var} - %{offset} + \
                1) in Bigarray.Array1.fill (Bigarray.Array1.sub %{array} \
                (%{first_index#Int} + %{offset}) %{var}) %{expr env ty}; %{read array}"])
         ])
  in
  [%string
    "(%{size_lets}let %{array} = %{module_}.init %{kind} %{spaces size_vars} (fun \
     %{init_param_decls} -> %{init}) in %{body})"]
;;

let forms ctx env ty gen =
  boost
    (if on "bigarrays" && List.mem ty [ Int; Float; Int64; Char; Num I32; Num Nat ]
     then [ (fun () -> bigarray ctx env ty gen) ]
     else [])
;;
