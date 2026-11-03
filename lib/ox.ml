open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Env

(* The body's type is immediate, so no local escapes. *)
let local_binding ctx env ty g =
  let e = g.e in
  let x = fresh ctx "l" in
  let boxed = { any with boxed = true } in
  let allocation s env =
    match s with
    | Pair (a, b) -> Some (fun () -> [%string "(%{e env a}, %{e env b})"])
    | List t -> Some (fun () -> [%string "(%{e env t} :: %{e env s})"])
    | Option t -> Some (fun () -> [%string "(Some %{e env t})"])
    | Named i ->
      (match ctx.decls.(i) with
       | Record fields ->
         Some (fun () -> [%string "{ %{field_values (e env) (field_types fields)} }"])
       | Variant constrs ->
         (match List.filter (fun (_, args) -> args <> []) constrs with
          | [] -> None
          | constrs ->
            Some
              (fun () ->
                let c, args = pick ctx constrs in
                construct c (List.map (e env) args)))
       | URecord _ -> None)
    | _ -> None
  in
  let mk = fresh ctx "mk" in
  let z = fresh ctx "z" in
  (* an allocation's type is drawn with it, as an expression's is *)
  let s, source =
    choose
      ctx
      [ (fun () -> g.free env (Any boxed))
      ; (fun () ->
          let s = decode ctx boxed in
          ( s
          , match allocation s env with
            | Some here -> [%string "stack_ %{here ()}"]
            | None -> e env s ))
      ; (fun () ->
          let s = decode ctx boxed in
          ( s
          , match allocation s (bind (closure env) z Int) with
            | Some there ->
              [%string
                "(let[@inline never] %{mk} (%{z} : int) = exclave_ (stack_ %{there ()}) \
                 in %{mk} %{e env Int})"]
            | None -> e env s ))
      ]
  in
  [%string "(let local_ %{x} : %{s#Ty} = %{source} in %{e (bind_local env x s) ty})"]
;;

let ox_forms ctx env ty g =
  let e = g.e in
  (if on "utuples"
   then
     [ (fun () ->
         let utuples =
           candidates ctx env (function
             | UTuple ts as t when List.mem ty ts -> Some t
             | _ -> None)
         in
         let first = flip ctx in
         let shape =
           UTuple_of (if first then [ Is ty; Any top ] else [ Any top; Is ty ])
         in
         let uts, tuple = g.free ~candidates:utuples env shape in
         let ts =
           match uts with
           | UTuple ts -> ts
           | _ -> assert false
         in
         let xs = List.map (fun t -> fresh ctx "u", t) ts in
         let names = String.concat ", " (List.map fst xs) in
         [%string "(let #(%{names}) = %{tuple} in %{e (bind_all env xs) ty})"])
     ]
   else [])
  @ (if on "or_null"
     then
       [ (fun () ->
           let nulls =
             candidates ctx env (function
               | Or_null _ as t -> Some t
               | _ -> None)
           in
           let os, o = g.free ~candidates:nulls env (Or_null_of (Any any)) in
           let s =
             match os with
             | Or_null s -> s
             | _ -> assert false
           in
           let x = fresh ctx "x" in
           let this = e (bind env x s) ty in
           [%string "(match %{o} with Null -> %{e env ty} | This %{x} -> %{this})"])
       ]
     else [])
  @
  if
    on "mutables"
    &&
    match ty with
    | UTuple _ | Or_null _ -> false
    | Named i -> not !urec.(i)
    | _ -> true
  then
    [ (fun () ->
        let x = fresh ctx "mu" in
        let i = fresh ctx "i" in
        let env' = { (bind env i Int) with muts = (x, ty) :: env.muts } in
        [%string
          "(let mutable %{x} : %{ty#Ty} = %{e env ty} in for %{i} = 0 to (%{e env Int} \
           land 7) do %{x} <- %{e env' ty} done; %{x})"])
    ]
  else []
;;

(* A number of another type, converted to [t]. *)
let converted env t g () =
  let s, x =
    g.free env (Any { any with only = Some ([ Int; Int64; Float ] @ newer_nums) })
  in
  convert s t x
;;

let num_ops ctx env t g =
  let e = g.e in
  let m = num_module t in
  let call f args () =
    [%string {|(%{m}.%{f} %{String.concat " " (List.map (e env) args)})|}]
  in
  converted env t g
  ::
  (if is_float t
   then
     [ call "add" [ t; t ]
     ; call "sub" [ t; t ]
     ; call "div" [ t; t ]
     ; call "neg" [ t ]
     ; call "abs" [ t ]
     ; call "sqrt" [ t ] (* opaque so arm64 cannot fuse the product into an fmadd *)
     ; (fun () ->
         let b = boxed_of t in
         convert
           b
           t
           (let product = [%string "(%{m}.mul %{e env t} %{e env t})"] in
            [%string "(Sys.opaque_identity %{convert t b product})"]))
     ]
   else
     List.map
       (fun f -> call f [ t; t ])
       [ "add"; "sub"; "mul"; "logand"; "logor"; "logxor" ]
     @ [ call "neg" [ t ]
       ; (fun () ->
           let w = width t in
           let sh = pick ctx [ "shift_left"; "shift_right"; "shift_right_logical" ] in
           let count =
             choose
               ctx
               [ (fun () -> string_of_int (pick ctx [ 0; 1; w - 2; w - 1 ]))
               ; (fun () ->
                   [%string "(%{e env Int} land %{if w = 63 then 31 else w - 1#Int})"])
               ]
           in
           [%string "(%{m}.%{sh} %{e env t} %{count})"])
       ])
;;

let num_compare ctx env g =
  let t, x = g.free env (Any { any with only = Some newer_nums }) in
  let hub = if is_float t then Float else Int64 in
  let m = if is_float t then "Float" else "Int64" in
  let a = convert t hub x in
  let b = convert t hub (g.e env t) in
  choose
    ctx
    [ (fun () -> [%string "(%{m}.compare %{a} %{b} < 0)"])
    ; (fun () -> [%string "(%{m}.equal %{a} %{b})"])
    ]
;;
