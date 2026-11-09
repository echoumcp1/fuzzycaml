(* Forms that build a value of any type [ty]. *)
open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Pattern
open Env

(* A variable bound by matching a local value is local too, unless it is
   immediate. *)
let bind_part local env var var_ty =
  if local && not (immediate var_ty)
  then bind_local env var var_ty
  else bind env var var_ty
;;

let recursion_attribute ctx =
  pick
    ctx
    ([ ""; "[@inline never]"; "[@inline always]"; "[@specialise]" ]
     @ if !ox_mode then [ "[@unrolled 2]"; "[@loop always]" ] else [])
;;

let call_with_attribute ctx fn =
  choose
    ctx
    [ (fun () -> fn)
    ; (fun () -> [%string "(%{fn} [@inlined never])"])
    ; (fun () -> [%string "(%{fn} [@inlined])"])
    ]
;;

let if_then_else env ty gen =
  let expr = gen.expr in
  [%string "(if %{expr env Bool} then %{expr env ty} else %{expr env ty})"]
;;

let let_binding ctx env ty gen =
  let bound_ty, rhs =
    gen.of_shape ~candidates:(candidates ctx env some_ty) env (Any all_types)
  in
  let var = fresh ctx "x" in
  [%string
    "(let %{var} : %{bound_ty#Ty} = %{rhs} in %{gen.expr (bind env var bound_ty) ty})"]
;;

let application ctx env ty gen =
  let arg_tys =
    candidates ctx env (function
      | Arrow (arg_ty, result_ty) when result_ty = ty -> Some arg_ty
      | _ -> None)
  in
  let arg_ty, arg = gen.of_shape ~candidates:arg_tys env (Any all_types) in
  [%string "(%{gen.expr env (Arrow (arg_ty, ty))} %{arg})"]
;;

let applied_lambda ctx env ty gen =
  let param_ty, arg = gen.of_shape env (Any all_types) in
  let param = fresh ctx "x" in
  let body = gen.expr (bind (closure env) param param_ty) ty in
  [%string "((fun (%{param} : %{param_ty#Ty}) -> %{body}) %{arg})"]
;;

let list_match ctx env ty gen =
  let expr = gen.expr in
  let list_ty, list, local =
    gen.scrutinee ~candidates:(candidates ctx env lists) env (List_of (Any value_types))
  in
  let elem_ty = elem_of list_ty in
  let head = fresh ctx "h" in
  let tail = fresh ctx "t" in
  let cons_env = bind_part local (bind_part local env head elem_ty) tail list_ty in
  [%string
    "(match %{list} with [] -> %{expr env ty} | %{head} :: %{tail} -> %{expr cons_env \
     ty})"]
;;

let option_match ctx env ty gen =
  let expr = gen.expr in
  let options =
    candidates ctx env (function
      | Option _ as option_ty -> Some option_ty
      | _ -> None)
  in
  let option_ty, option, local =
    gen.scrutinee ~candidates:options env (Option_of (Any value_types))
  in
  let content_ty =
    match option_ty with
    | Option content_ty -> content_ty
    | _ -> assert false
  in
  let var = fresh ctx "x" in
  let some_env = bind_part local env var content_ty in
  [%string
    "(match %{option} with None -> %{expr env ty} | Some %{var} -> %{expr some_env ty})"]
;;

let pair_destructure ctx env ty gen =
  let pairs =
    candidates ctx env (function
      | Pair _ as pair_ty -> Some pair_ty
      | _ -> None)
  in
  let pair_ty, pair, local =
    gen.scrutinee ~candidates:pairs env (Pair_of (Any value_types, Any value_types))
  in
  let first_ty, second_ty =
    match pair_ty with
    | Pair (first_ty, second_ty) -> first_ty, second_ty
    | _ -> assert false
  in
  let first = fresh ctx "x" in
  let second = fresh ctx "y" in
  let body_env = bind_part local (bind_part local env first first_ty) second second_ty in
  [%string "(let (%{first}, %{second}) = %{pair} in %{gen.expr body_env ty})"]
;;

let accumulating_recursion ctx env ty gen =
  let expr = gen.expr in
  let fn = fresh ctx "go" in
  let count = fresh ctx "n" in
  let acc = fresh ctx "acc" in
  let env = closure env in
  let body_env = bind (bind env count Int) acc ty in
  [%string
    "(let%{recursion_attribute ctx} rec %{fn} (%{count} : int) (%{acc} : %{ty#Ty}) : \
     %{ty#Ty} = if %{count} <= 0 then %{acc} else %{fn} (%{count} - 1) %{expr body_env \
     ty} in %{call_with_attribute ctx fn} (%{expr env Int} land 15) %{expr env ty})"]
;;

let non_tail_recursion ctx env ty gen =
  let expr = gen.expr in
  let fn = fresh ctx "go" in
  let count = fresh ctx "n" in
  let result = fresh ctx "r" in
  let env = closure env in
  let count_expr = expr env Int in
  let call = call_with_attribute ctx fn in
  let step = expr (bind (bind env count Int) result ty) ty in
  let base = expr (bind env count Int) ty in
  [%string
    "(let%{recursion_attribute ctx} rec %{fn} (%{count} : int) : %{ty#Ty} = if %{count} \
     <= 0 then %{base} else (let %{result} : %{ty#Ty} = %{fn} (%{count} - 1) in %{step}) \
     in %{call} (%{count_expr} land 15))"]
;;

let exit_handler env ty gen =
  let expr = gen.expr in
  if on "exits"
  then (
    let body = expr { env with in_try = true } ty in
    [%string "(try %{body} with Exit -> %{expr env ty})"])
  else [%string "(if %{expr env Bool} then %{expr env ty} else %{expr env ty})"]
;;

(* A match-in-match: the inner match's scrutinee is opaque, so its result
   constructor is unknown, but each arm builds a known one. *)
let match_in_match ctx env gen ~variants decl =
  let expr = gen.expr in
  let outer_constructors = List.assoc decl variants in
  let inner_decl, inner_constructors = pick ctx variants in
  let offset = int_in ctx 0 (List.length outer_constructors - 1) in
  let arm index (constructor, args) =
    let result_constructor, result_args =
      List.nth outer_constructors ((index + offset) mod List.length outer_constructors)
    in
    let pattern = construct constructor (List.map (fun _ -> "_") args) in
    [%string
      "| %{pattern} -> %{construct result_constructor (List.map (expr env) result_args)}"]
  in
  let arms = String.concat " " (List.mapi arm inner_constructors) in
  [%string "(match Sys.opaque_identity %{expr env (Named inner_decl)} with %{arms})"]
;;

let pattern_match ctx env ty gen =
  let expr = gen.expr in
  let named =
    candidates ctx env (function
      | Named _ as named_ty -> Some named_ty
      | _ -> None)
  in
  let named = if named <> [] then named else candidates ctx env some_ty in
  let variants =
    List.filter_map
      (fun (decl, decl_def) ->
         match decl_def with
         | Variant constructors -> Some (decl, constructors)
         | _ -> None)
      (indexed_decls ctx)
  in
  let tuple = flip ~p:0.4 ctx in
  let nested = flip ~p:0.3 ctx in
  let alternative_scrutinee = function
    | Pair (first_ty, second_ty) when tuple ->
      Some (fun () -> [%string "%{expr env first_ty}, %{expr env second_ty}"])
    | Named decl when nested && List.mem_assoc decl variants ->
      Some (fun () -> match_in_match ctx env gen ~variants decl)
    | _ -> None
  in
  (* An exception arm catches what the scrutinee raises. *)
  let exn_arm = on "exits" && flip ~p:0.2 ctx in
  let scrutinee_ty, scrutinee, local =
    gen.scrutinee
      ~candidates:named
      ~alt:alternative_scrutinee
      (if exn_arm then { env with in_try = true } else env)
      (Any all_types)
  in
  let arm () =
    let pattern, bound = pattern ~at_root:true ctx scrutinee_ty 3 ~binds:true in
    let arm_env =
      List.fold_left (fun env (var, var_ty) -> bind_part local env var var_ty) env bound
    in
    let guard = if flip ~p:0.3 ctx then [%string " when %{expr arm_env Bool}"] else "" in
    [%string "| %{pattern}%{guard} -> %{expr arm_env ty}"]
  in
  let arms = List.init (int_in ctx 1 4) (fun _ -> arm ()) in
  let in_arm = exn_arm && (not local) && not (restricted scrutinee_ty) in
  let arms =
    String.concat
      " "
      (if in_arm then arms @ [ [%string "| exception Exit -> %{expr env ty}"] ] else arms)
  in
  let whole =
    if flip ~p:0.6 ctx
    then (
      let var = fresh ctx "m" in
      [%string
        "(match %{scrutinee} with %{arms} | %{var} -> %{expr (bind_part local env var \
         scrutinee_ty) ty})"])
    else
      (* Without a catch-all the match may fail, so a Match_failure handler goes
         around it. *)
      [%string
        "(try (match %{scrutinee} with %{arms}) with Match_failure _ -> %{expr env ty})"]
  in
  if exn_arm && not in_arm
  then [%string "(try %{whole} with Exit -> %{expr env ty})"]
  else whole
;;

let opaque env ty gen =
  if on "opaque"
  then [%string "(Sys.opaque_identity %{gen.expr env ty})"]
  else gen.expr env ty
;;

let first_of_pair ctx env ty gen =
  let pairs =
    candidates ctx env (function
      | Pair (first_ty, _) as pair_ty when first_ty = ty -> Some pair_ty
      | _ -> None)
  in
  let _, pair = gen.of_shape ~candidates:pairs env (Pair_of (Is ty, Any value_types)) in
  [%string "(fst %{pair})"]
;;

let second_of_pair ctx env ty gen =
  let pairs =
    candidates ctx env (function
      | Pair (_, second_ty) as pair_ty when second_ty = ty -> Some pair_ty
      | _ -> None)
  in
  let _, pair = gen.of_shape ~candidates:pairs env (Pair_of (Any value_types, Is ty)) in
  [%string "(snd %{pair})"]
;;

let list_fold ctx env ty gen =
  let expr = gen.expr in
  let list_ty, list =
    gen.of_shape ~candidates:(candidates ctx env lists) env (List_of (Any value_types))
  in
  let elem_ty = elem_of list_ty in
  let acc = fresh ctx "acc" in
  let elem = fresh ctx "x" in
  let init = expr env ty in
  let step = expr (bind (bind (closure env) acc ty) elem elem_ty) ty in
  [%string
    "(List.fold_left (fun (%{acc} : %{ty#Ty}) (%{elem} : %{elem_ty#Ty}) -> %{step}) \
     %{init} %{list})"]
;;

let field_reads env ty gen decls =
  List.concat_map
    (fun (decl, decl_def) ->
       match decl_def with
       | Record fields ->
         List.filter_map
           (fun (field : record_field) ->
              if field.ty = ty
              then
                Some
                  (fun () ->
                    (* A local record's field is local unless it is immediate. *)
                    let record =
                      if immediate field.ty
                      then (
                        let _, record, _ = gen.scrutinee env (Is (Named decl)) in
                        record)
                      else gen.expr env (Named decl)
                    in
                    [%string "(%{record}).%{field.name}"])
              else None)
           fields
       | URecord fields ->
         List.filter_map
           (fun (field, field_ty) ->
              if field_ty = ty
              then (
                let dot = ox_syntax ".#" "." in
                Some (fun () -> [%string "(%{gen.expr env (Named decl)})%{dot}%{field}"]))
              else None)
           fields
       | Variant _ -> [])
    decls
;;

let array_reads ctx env ty gen =
  let expr = gen.expr in
  let readable =
    on "arrays"
    &&
    if !ox_mode
    then
      is_num ty
      ||
      match ty with
      | Arr _ -> true
      | UTuple component_tys -> on "arrays" && array_product component_tys
      | _ -> false
    else not (restricted ty)
  in
  if not readable
  then []
  else
    [ (fun () ->
        let array = fresh ctx "a" in
        [%string
          "(let %{array} = %{expr env (Arr ty)} in array_get %{array} ((%{expr env Int} \
           land max_int) mod array_length %{array}))"])
    ]
    @
    match ty with
    | Float | Int ->
      [ (fun () ->
          let witness = if ty = Float then "AwFloat" else "AwInt" in
          [%string "(arr_get %{witness} %{expr env (Arr ty)} %{expr env Int})"])
      ]
    | _ -> []
;;

let variant_upcasts env ty gen =
  List.filter_map
    (fun (child, parent) ->
       if Named child = ty
       then
         Some
           (fun () ->
             [%string
               "(%{gen.expr env (Named parent)} : t%{parent#Int} :> t%{child#Int})"])
       else None)
    !extended_variants
;;

(* Both branches are equal, so the optimizer can join them. *)
let same_branches env ty gen =
  if on "samebranch"
  then
    [ (fun () ->
        let condition = gen.expr env Bool in
        let branch = gen.expr env ty in
        [%string "(if %{condition} then %{branch} else %{branch})"])
    ]
  else []
;;

let generic ctx env ty gen =
  [ (fun () -> if_then_else env ty gen)
  ; (fun () -> let_binding ctx env ty gen)
  ; (fun () -> application ctx env ty gen)
  ; (fun () -> applied_lambda ctx env ty gen)
  ; (fun () -> list_match ctx env ty gen)
  ; (fun () -> option_match ctx env ty gen)
  ; (fun () -> pair_destructure ctx env ty gen)
  ; (fun () -> accumulating_recursion ctx env ty gen)
  ; (fun () -> non_tail_recursion ctx env ty gen)
  ; (fun () -> exit_handler env ty gen)
  ; (fun () -> pattern_match ctx env ty gen)
  ]
  @ (if restricted ty
     then []
     else
       [ (fun () -> opaque env ty gen)
       ; (fun () -> first_of_pair ctx env ty gen)
       ; (fun () -> second_of_pair ctx env ty gen)
       ; (fun () -> list_fold ctx env ty gen)
       ])
  @ field_reads env ty gen (indexed_decls ctx)
  @ array_reads ctx env ty gen
  @ Ox.forms ctx env ty gen
  @ gate env.in_try [ (fun () -> raise_at ctx ty) ]
  @ Locals.forms ctx env ty gen
  @ Partial.forms ctx env ty gen
  @ Ticks.forms ctx env ty gen
  @ Effects.forms ctx env ty gen
  @ Laziness.forms ctx env ty gen
  @ Rec_values.forms ctx env ty gen
  @ Strings.forms ctx env ty gen
  @ Gadt.forms ctx env ty gen
  @ boost (variant_upcasts env ty gen)
  @ Atomics.forms ctx env ty gen
  @ Objects.forms ctx env ty gen
  @ Bigarrays.forms ctx env ty gen
  @ Comprehensions.forms ctx env ty gen
  @ Simd.forms ctx env ty gen
  @ Functors.forms ctx env ty gen
  @ Stress.forms ctx env ty gen
  @ Exceptions.forms ctx env ty gen
  @ boost (same_branches env ty gen)
  @ Loops.forms ctx env ty gen
;;
