open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Env

(* [let local_ x = ... in body], where the value is ordinary, a [stack_]
   allocation, or allocated by a helper in the caller's region with [exclave_].
   The body's type is immediate, so no local escapes. *)
let local_binding ctx env ty e =
  let s =
    match any_ty ctx with
    | (List _ | Option _ | Pair _ | Named _) as t -> t
    | t -> Option t
  in
  let x = fresh ctx "l" in
  let allocation env =
    match s with
    | Pair (a, b) -> Some (fun () -> [%string "(%{e env a}, %{e env b})"])
    | List t -> Some (fun () -> [%string "(%{e env t} :: %{e env s})"])
    | Option t -> Some (fun () -> [%string "(Some %{e env t})"])
    | Named i ->
      (match ctx.decls.(i) with
       | Record fields ->
         Some
           (fun () ->
             p
               "{ %s }"
               (String.concat
                  "; "
                  (List.map (fun (f, t, _) -> [%string "%{f} = %{e env t}"]) fields)))
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
  let source =
    let mk = fresh ctx "mk" in
    let z = fresh ctx "z" in
    choose
      ctx
      ((fun () -> e env s)
       ::
       (match allocation env, allocation (bind (closure env) z Int) with
        | Some here, Some there ->
          [ (fun () -> [%string "stack_ %{here ()}"])
          ; (fun () ->
              [%string
                "(let[@inline never] %{mk} (%{z} : int) = exclave_ (stack_ %{there ()}) \
                 in %{mk} %{e env Int})"])
          ]
        | _ -> []))
  in
  [%string "(let local_ %{x} : %{s#Ty} = %{source} in %{e (bind_local env x s) ty})"]
;;

(* OxCaml forms at any type: destructuring an unboxed tuple or an or_null, and
   a [let mutable] updated in a loop. *)
let ox_forms ctx env ty e =
  (if on "utuples"
   then
     [ (fun () ->
         let ts =
           from_env
             ctx
             env
             (function
               | UTuple ts when List.mem ty ts -> Some ts
               | _ -> None)
             (fun () -> if flip ctx then [ ty; top_ty ctx ] else [ top_ty ctx; ty ])
         in
         let xs = List.map (fun t -> fresh ctx "u", t) ts in
         let names = String.concat ", " (List.map fst xs) in
         [%string "(let #(%{names}) = %{e env (UTuple ts)} in %{e (bind_all env xs) ty})"])
     ]
   else [])
  @ (if on "or_null"
     then
       [ (fun () ->
           let s =
             env_ty ctx env (function
               | Or_null s -> Some s
               | _ -> None)
           in
           let x = fresh ctx "x" in
           [%string
             "(match %{e env (Or_null s)} with Null -> %{e env ty} | This %{x} -> %{e \
              (bind env x s) ty})"])
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

(* Arithmetic on the newer number types, and conversions into them. *)
let num_ops ctx env t e =
  let m = num_module t in
  let call f args () =
    [%string {|(%{m}.%{f} %{String.concat " " (List.map (e env) args)})|}]
  in
  let from () =
    let s = pick ctx ([ Int; Int64; Float ] @ newer_nums) in
    convert s t (e env s)
  in
  from
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

(* Comparing two numbers of one of the newer types, through int64 or float. *)
let num_compare ctx env e =
  let t = pick ctx newer_nums in
  let hub = if is_float t then Float else Int64 in
  let m = if is_float t then "Float" else "Int64" in
  let a = convert t hub (e env t) in
  let b = convert t hub (e env t) in
  choose
    ctx
    [ (fun () -> [%string "(%{m}.compare %{a} %{b} < 0)"])
    ; (fun () -> [%string "(%{m}.equal %{a} %{b})"])
    ]
;;
