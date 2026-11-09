open Config
open Ty
open Ctx
open Env

(* A lane of a tree of vector ops, built from lanes of generated values. *)
let simd ctx env ty gen =
  let expr = gen.expr in
  let rec vector_tree depth vector =
    let module_ = Neon.name vector in
    let leaf () =
      let lane = fresh ctx "i" in
      [%string
        "(%{module_}.init (fun (%{lane} : int) -> %{expr (bind (closure env) lane Int) \
         (Neon.lane vector)}))"]
    in
    if depth = 0
    then leaf ()
    else (
      let smaller = vector_tree (depth - 1) in
      let op () =
        let { Neon.name = op; shape; _ } = pick ctx (Neon.ops vector) in
        match shape with
        | Unary -> [%string "(%{module_}.%{op} %{smaller vector})"]
        | Binary ->
          if flip ~p:0.2 ctx
          then (
            let shared = fresh ctx "v" in
            [%string
              "(let %{shared} = %{smaller vector} in %{module_}.%{op} %{shared} \
               %{shared})"])
          else [%string "(%{module_}.%{op} %{smaller vector} %{smaller vector})"]
        | Shift ->
          [%string
            "(%{module_}.%{op} %{int_in ctx 1 (Neon.width vector - 1)#Int} %{smaller \
             vector})"]
        | From_one source -> [%string "(%{module_}.%{op} %{smaller source})"]
        | From_two (source, other_source) ->
          [%string "(%{module_}.%{op} %{smaller source} %{smaller other_source})"]
      in
      choose
        ctx
        [ leaf
        ; (fun () -> [%string "(%{module_}.opaque %{smaller vector})"])
        ; op
        ; op
        ; op
        ])
  in
  let vector = pick ctx Neon.all in
  let to_result =
    match Neon.lane vector, ty with
    | Int, Int64 -> "Int64.of_int"
    | Int, Float -> "float_of_int"
    | Int64, Int -> "Int64.to_int"
    | Int64, Float -> "Int64.to_float"
    | Float, Int -> "(fun f -> Int64.to_int (fsat 64 f))"
    | Float, Int64 -> "fsat 64"
    | _ -> ""
  in
  let result = fresh ctx "v" in
  [%string
    "(let %{result} = %{vector_tree (int_in ctx 1 3) vector} in %{to_result} \
     (%{Neon.name vector}.get %{result} %{paren (expr env Int)}))"]
;;

let forms ctx env ty gen =
  boost
    (if !props && !neon && on "simd" && List.mem ty [ Int; Int64; Float ]
     then [ (fun () -> simd ctx env ty gen) ]
     else [])
;;
