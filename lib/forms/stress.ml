open Config
open Ty
open Ctx
open Gen_ty
open Env

type binding =
  { var : string
  ; var_ty : ty
  ; value : string
  }

let bindings ctx gen env count params prefix =
  List.init count (fun _ ->
    let var_ty, value = gen.of_shape env (Any params) in
    { var = fresh ctx (prefix var_ty); var_ty; value })
;;

let lets bindings =
  String.concat
    ""
    (List.map
       (fun { var; var_ty; value } ->
          [%string "let %{var} : %{var_ty#Ty} = %{value} in "])
       bindings)
;;

let types bindings = List.map (fun binding -> binding.var, binding.var_ty) bindings

(* Many ints and floats live across an opaque call, so some must be spilled. *)
let pressure ctx env ty gen =
  let expr = gen.expr in
  let count = int_in ctx 8 20 in
  let vars =
    bindings
      ctx
      gen
      env
      count
      { value_types with only = Some [ Int; Float ] }
      (fun var_ty -> if var_ty = Int then "i" else "f")
  in
  let typed_vars = types vars in
  let parity = fresh ctx "k" in
  let body_env = bind_all (bind env parity Int) typed_vars in
  let sum var_ty plus zero =
    match List.filter (fun (_, t') -> t' = var_ty) typed_vars with
    | [] -> zero
    | matching -> String.concat plus (List.map fst matching)
  in
  let ints = sum Int " + " "0" in
  let floats = sum Float " +. " "0." in
  let else_ = expr body_env ty in
  let then_ = expr body_env ty in
  (* Each int flips the branch, where an equality would almost never hold. *)
  [%string
    "(%{lets vars} let %{parity} = (Sys.opaque_identity succ) %{expr env Int} in if \
     ((%{ints} + %{parity}) land 1 = 0) <> (%{floats} > float_of_int %{parity}) then \
     %{then_} else %{else_})"]
;;

(* More int and float parameters than arm64 passes in registers, in a
   function that calls itself in tail position. Arguments are let-bound
   because their evaluation order is unspecified. *)
let many_args ctx env ty gen =
  let expr = gen.expr in
  let fn = fresh ctx "go" in
  let remaining = fresh ctx "n" in
  let env = closure env in
  let first_count = fresh ctx "m" in
  let first_args =
    List.init (int_in ctx 9 14) (fun _ ->
      let var_ty, value =
        gen.of_shape ~candidates:[ Int; Float ] ~p:0.67 env (Any first_order_types)
      in
      { var = fresh ctx "b"; var_ty; value })
  in
  let params = List.map (fun arg -> fresh ctx "a", arg.var_ty) first_args in
  let body_env = bind_all (bind env remaining Int) params in
  (* Recursive calls mostly pass parameters through, to keep programs small. *)
  let arg arg_ty =
    let same_type = List.filter (fun (_, t') -> t' = arg_ty) params in
    if flip ~p:0.3 ctx then expr body_env arg_ty else fst (pick ctx same_type)
  in
  let inner_args =
    List.map
      (fun (_, var_ty) ->
         let value = arg var_ty in
         { var = fresh ctx "b"; var_ty; value })
      params
  in
  let outer_lets = lets first_args in
  let outer_args =
    String.concat " " (first_count :: List.map (fun arg -> arg.var) first_args)
  in
  let inner_lets = lets inner_args in
  let recursive_args =
    String.concat
      " "
      ([%string "(%{remaining} - 1)"] :: List.map (fun arg -> arg.var) inner_args)
  in
  let head =
    choose ctx [ (fun () -> fn); (fun () -> [%string "(%{fn} [@inlined never])"]) ]
  in
  let count_expr = expr env Int in
  let base = expr body_env ty in
  let attr = pick ctx [ ""; "[@inline never]" ] in
  let decls =
    String.concat
      " "
      (List.map (fun (x, arg_ty) -> [%string "(%{x} : %{arg_ty#Ty})"]) params)
  in
  [%string
    "(let%{attr} rec %{fn} (%{remaining} : int) %{decls} : %{ty#Ty} = if %{remaining} <= \
     0 then %{base} else (%{inner_lets}%{fn} %{recursive_args}) in let %{first_count} = \
     %{count_expr} land 7 in %{outer_lets}%{head} %{outer_args})"]
;;

(* A million calls in tail position, which overflow the stack programs run with
   unless each is a tail call. The loop only passes values through, so that it
   stays fast. *)
let tail_loop ctx env ty gen =
  let fn = fresh ctx "go" in
  let other = fresh ctx "go" in
  let n = fresh ctx "n" in
  let acc = fresh ctx "acc" in
  let mutual = flip ctx in
  let callee = if mutual then other else fn in
  let call () =
    pick
      ctx
      [ [%string "%{callee} (%{n} - 1) %{acc}"]
      ; [%string "(Sys.opaque_identity %{callee}) (%{n} - 1) %{acc}"]
      ]
  in
  let opaque_n = [%string "Sys.opaque_identity %{n}"] in
  let rec step depth =
    let inner () = if depth = 0 then call () else step (depth - 1) in
    choose
      ctx
      ([ (fun () -> [%string "(if %{n} land 1 = 0 then %{inner ()} else %{inner ()})"])
       ; (fun () ->
           [%string
             "(match %{n} land 3 with 0 -> %{inner ()} | 1 -> %{inner ()} | _ -> %{inner \
              ()})"])
       ; (fun () ->
           let x = fresh ctx "x" in
           [%string
             "(let %{x} = %{n} + 1 in if Sys.opaque_identity %{x} = 0 then %{acc} else \
              %{inner ()})"])
       ; (fun () -> [%string "(ignore (%{opaque_n}); %{inner ()})"])
       ; (fun () -> [%string "((try ignore (%{opaque_n}) with Exit -> ()); %{inner ()})"])
       ; (fun () ->
           [%string
             "(match %{opaque_n} with _ -> %{inner ()} | exception Exit -> %{acc})"])
       ; (fun () -> [%string "(%{inner ()} : %{ty#Ty})"])
       ]
       @
       if !ox_mode && on "locals"
       then
         [ (fun () ->
             let r = fresh ctx "r" in
             let local = ox_syntax "local_ " "" in
             [%string
               "(let %{local}%{r} = ref %{n} in ignore (Sys.opaque_identity !%{r}); \
                %{inner ()})"])
         ]
       else [])
  in
  let signature = [%string "(%{n} : int) (%{acc} : %{ty#Ty}) : %{ty#Ty}"] in
  let other_def =
    if mutual then [%string " and %{other} %{signature} = %{fn} %{n} %{acc}"] else ""
  in
  let attr = pick ctx [ ""; "[@inline never]" ] in
  let body = step (int_in ctx 0 2) in
  [%string
    "(let%{attr} rec %{fn} %{signature} = if %{n} <= 0 then %{acc} else \
     %{body}%{other_def} in %{fn} 1_000_000 %{gen.expr env ty})"]
;;

(* Fresh allocations live across a collection and are used afterward, so the GC
   must find them wherever the backend keeps them, and skip the unboxed values
   among them. *)
let gc ctx env ty gen =
  let allocations = bindings ctx gen env (int_in ctx 2 6) all_types (fun _ -> "g") in
  let gc =
    pick ctx [ "Gc.minor ()"; "Gc.minor ()"; "Gc.full_major ()"; "Gc.compact ()" ]
  in
  [%string
    "(%{lets allocations}%{gc}; %{gen.expr (bind_all env (types allocations)) ty})"]
;;

(* A collection promotes a block, which then holds a younger value, so the store
   must record it for the next collection to find. *)
let barrier ctx env ty gen =
  let expr = gen.expr in
  let stored () = [%string "(%{expr env ty} : %{ty#Ty})"] in
  let array () =
    let container = fresh ctx "c" in
    let index = fresh ctx "i" in
    (* An array of more than 256 words, which even 8-bit elements reach at 2049,
       is allocated in the major heap directly. *)
    let base = pick ctx [ 1; 2049 ] in
    [%string
      "(let %{container} = array_make (%{base#Int} + (%{expr env Int} land 7)) %{stored \
       ()} in Gc.minor (); let %{index} = (%{expr env Int} land max_int) mod \
       array_length %{container} in array_set %{container} %{index} %{stored ()}; \
       Gc.minor (); array_get %{container} %{index})"]
  in
  let field decl (field : record_field) () =
    let container = fresh ctx "c" in
    [%string
      "(let %{container} = %{fresh_record ctx env gen decl} in Gc.minor (); \
       %{container}.%{field.name} <- %{stored ()}; Gc.minor (); \
       %{container}.%{field.name})"]
  in
  (if array_elem ctx ty then [ array ] else [])
  @ List.concat_map
      (fun (decl, decl_def) ->
         match decl_def with
         | Record fields ->
           List.filter_map
             (fun (f : record_field) ->
                if f.is_mutable && f.ty = ty then Some (field decl f) else None)
             fields
         | URecord _ | Variant _ -> [])
      (indexed_decls ctx)
;;

(* The runtime copies, measures, weakly holds or finalises [x], walking it by its
   layout. *)
let walk ctx x ty =
  choose
    ctx
    [ (fun () ->
        [%string
          "(if Obj.is_block (Obj.repr %{x}) then (Obj.obj (Obj.dup (Obj.repr %{x})) : \
           %{ty#Ty}) else %{x})"])
    ; (fun () -> [%string "(ignore (Obj.reachable_words (Obj.repr %{x})); %{x})"])
    ; (fun () ->
        let get = pick ctx [ "Weak.get"; "Weak.get_copy" ] in
        [%string
          "(let w = Weak.create 1 in Weak.set w 0 (Some %{x}); Gc.full_major (); match \
           %{get} w 0 with Some y -> y | None -> %{x})"])
    ; (fun () ->
        [%string
          "(let k = ref 0 in let e = Ephemeron.K1.make k %{x} in Gc.full_major (); match \
           Ephemeron.K1.query e k with Some y -> y | None -> %{x})"])
      (* Some values cannot be finalised, and when the finaliser runs depends on
         the backend, so it does nothing visible. *)
    ; (fun () ->
        [%string
          "((try Gc.finalise (fun v -> ignore (Sys.opaque_identity v)) %{x} with \
           Invalid_argument _ -> ()); %{x})"])
    ]
;;

let walked ctx env ty gen =
  let x = fresh ctx "x" in
  [%string "(let %{x} : %{ty#Ty} = %{gen.expr env ty} in %{walk ctx x ty})"]
;;

(* Records with an unboxed field, which the runtime scans differently from other
   records. Few expressions have their type, so a fresh one is walked beside the
   expression, which can then read it. *)
let mixed_records ctx =
  List.filter_map
    (fun (decl, decl_def) ->
       match decl_def with
       | Record fields when List.exists (fun (f : record_field) -> restricted f.ty) fields
         -> Some decl
       | Record _ | URecord _ | Variant _ -> None)
    (indexed_decls ctx)
;;

let walked_mixed ctx env ty gen decls =
  let decl = pick ctx decls in
  let x = fresh ctx "x" in
  let record_ty = Named decl in
  let walked = walk ctx x record_ty in
  [%string
    "(let %{x} : %{record_ty#Ty} = %{fresh_record ctx env gen decl} in let %{x} : \
     %{record_ty#Ty} = %{walked} in %{gen.expr (bind env x record_ty) ty})"]
;;

(* An interrupt callback may raise in the middle of it, and then it runs again.
   [pure] leaves out lazies from outside, which, interrupted while forced, would
   raise [Sys.Break] again when the retry forces them. *)
let interrupted env ty gen = [%string "(attempt (fun () -> %{gen.expr (pure env) ty}))"]

let forms ctx env ty gen =
  let value = not (restricted ty) in
  (if first_order ty then [ (fun () -> pressure ctx env ty gen) ] else [])
  @ (if value && on "manyargs" then [ (fun () -> many_args ctx env ty gen) ] else [])
  (* Inside a function, the loop could run once per call. *)
  @ (if value && on "tailcalls" && not env.in_fun
     then [ (fun () -> tail_loop ctx env ty gen) ]
     else [])
  @ boost (if value && on "gc" then [ (fun () -> gc ctx env ty gen) ] else [])
  @ (if on "gc" then barrier ctx env ty gen else [])
  @ (let decls = mixed_records ctx in
     if on "gc" && decls <> []
     then [ (fun () -> walked_mixed ctx env ty gen decls) ]
     else [])
  @ boost
      (if value && on "interrupts" then [ (fun () -> interrupted env ty gen) ] else [])
  @
  match ty with
  | Arrow _ -> []
  | _ -> if value && on "gc" then [ (fun () -> walked ctx env ty gen) ] else []
;;
