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

(* Fresh allocations live across a collection and are used afterward, so the GC
   must find them wherever the backend keeps them. *)
let gc ctx env ty gen =
  let allocations =
    bindings ctx gen env (int_in ctx 2 6) first_order_types (fun _ -> "g")
  in
  let gc =
    pick ctx [ "Gc.minor ()"; "Gc.minor ()"; "Gc.full_major ()"; "Gc.compact ()" ]
  in
  [%string
    "(%{lets allocations}%{gc}; %{gen.expr (bind_all env (types allocations)) ty})"]
;;

(* An interrupt callback may raise in the middle of it, and then it runs again. A
   lazy from outside is left out: interrupted while forcing it, it would raise
   [Sys.Break] again when the retry forces it. *)
let interrupted env ty gen =
  let env = pure env in
  let env =
    { env with
      vars =
        List.filter
          (fun (var, _) -> not (String.starts_with ~prefix:"(Lazy.force " var))
          env.vars
    }
  in
  [%string "(attempt (fun () -> %{gen.expr env ty}))"]
;;

let forms ctx env ty gen =
  let value = not (restricted ty) in
  (if first_order ty then [ (fun () -> pressure ctx env ty gen) ] else [])
  @ (if value && on "manyargs" then [ (fun () -> many_args ctx env ty gen) ] else [])
  @ boost (if value && on "gc" then [ (fun () -> gc ctx env ty gen) ] else [])
  @ boost
      (if value && on "interrupts" then [ (fun () -> interrupted env ty gen) ] else [])
;;
