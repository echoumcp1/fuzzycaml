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
    | Pair (a, b) -> Some (fun () -> p "(%s, %s)" (e env a) (e env b))
    | List t -> Some (fun () -> p "(%s :: %s)" (e env t) (e env s))
    | Option t -> Some (fun () -> p "(Some %s)" (e env t))
    | Named i ->
      (match ctx.decls.(i) with
       | Record fields ->
         Some
           (fun () ->
             p
               "{ %s }"
               (String.concat
                  "; "
                  (List.map (fun (f, t, _) -> p "%s = %s" f (e env t)) fields)))
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
          [ (fun () -> p "stack_ %s" (here ()))
          ; (fun () ->
              p
                "(let[@inline never] %s (%s : int) = exclave_ (stack_ %s) in %s %s)"
                mk
                z
                (there ())
                mk
                (e env Int))
          ]
        | _ -> []))
  in
  p "(let local_ %s : %s = %s in %s)" x (show_ty s) source (e (bind_local env x s) ty)
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
         p
           "(let #(%s) = %s in %s)"
           (String.concat ", " (List.map fst xs))
           (e env (UTuple ts))
           (e (bind_all env xs) ty))
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
           p "(match %s with Null -> %s | This %s -> %s)" (e env (Or_null s)) (e env ty) x (e (bind env x s) ty))
       ]
     else [])
  @
  if on "mutables" && (match ty with UTuple _ | Or_null _ -> false | Named i -> not !urec.(i) | _ -> true)
  then
    [ (fun () ->
        let x = fresh ctx "mu" in
        let i = fresh ctx "i" in
        let env' = { (bind env i Int) with muts = (x, ty) :: env.muts } in
        p
          "(let mutable %s : %s = %s in for %s = 0 to (%s land 7) do %s <- %s done; %s)"
          x
          (show_ty ty)
          (e env ty)
          i
          (e env Int)
          x
          (e env' ty)
          x)
    ]
  else []
;;

(* Arithmetic on the newer number types, and conversions into them. *)
let num_ops ctx env t e =
  let m = num_module t in
  let call f args () = p "(%s.%s %s)" m f (String.concat " " (List.map (e env) args)) in
  let from () =
    let s = pick ctx ([ Int; Int64; Float ] @ newer_nums) in
    convert s t (e env s)
  in
  from
  :: (if is_float t
      then
        [ call "add" [ t; t ]; call "sub" [ t; t ]; call "div" [ t; t ]; call "neg" [ t ]; call "abs" [ t ]; call "sqrt" [ t ]
          (* opaque so arm64 cannot fuse the product into an fmadd *)
        ; (fun () ->
            let b = boxed_of t in
            convert b t (p "(Sys.opaque_identity %s)" (convert t b (p "(%s.mul %s %s)" m (e env t) (e env t)))))
        ]
      else
        List.map (fun f -> call f [ t; t ]) [ "add"; "sub"; "mul"; "logand"; "logor"; "logxor" ]
        @ [ call "neg" [ t ]
          ; (fun () ->
              let w = width t in
              let sh = pick ctx [ "shift_left"; "shift_right"; "shift_right_logical" ] in
              let count =
                choose
                  ctx
                  [ (fun () -> string_of_int (pick ctx [ 0; 1; w - 2; w - 1 ]))
                  ; (fun () -> p "(%s land %d)" (e env Int) (if w = 63 then 31 else w - 1))
                  ]
              in
              p "(%s.%s %s %s)" m sh (e env t) count)
          ])
;;

(* Comparing two numbers of one of the newer types, through int64 or float. *)
let num_compare ctx env e =
  let t = pick ctx newer_nums in
  let hub = if is_float t then Float else Int64 in
  let m = if is_float t then "Float" else "Int64" in
  let a = convert t hub (e env t) in
  let b = convert t hub (e env t) in
  choose ctx [ (fun () -> p "(%s.compare %s %s < 0)" m a b); (fun () -> p "(%s.equal %s %s)" m a b) ]
;;
