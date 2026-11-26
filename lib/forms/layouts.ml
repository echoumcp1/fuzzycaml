open Config
open Ty
open Ctx
open Gen_ty
open Env
open Printer

(* The kind of [ty], as an annotation spells it. *)
let rec kind ctx ty =
  let product = function
    | [ only ] -> only
    | kinds -> "(" ^ String.concat " & " kinds ^ ")"
  in
  match ty with
  | Unboxed UFloat -> "float64"
  | Unboxed UFloat32 -> "float32"
  | Unboxed UInt -> "untagged_immediate"
  | Unboxed UInt8 -> "bits8"
  | Unboxed UInt16 -> "bits16"
  | Unboxed UInt32 -> "bits32"
  | Unboxed UInt64 -> "bits64"
  | Unboxed UNativeint -> "word"
  | UTuple component_tys -> product (List.map (kind ctx) component_tys)
  | Or_null _ -> "value_or_null"
  | Named decl ->
    (match ctx.decls.(decl) with
     | URecord fields ->
       product (List.map (fun (_, field_ty) -> kind ctx field_ty) fields)
     | Record _ | Variant _ -> "value")
  | Int
  | Bool
  | Float
  | Char
  | Int64
  | Str
  | List _
  | Option _
  | Pair _
  | Arrow _
  | Num _
  | Arr _ -> "value"
;;

let of_kind ctx ty = ox_syntax (" : " ^ kind ctx ty) ""

(* Bound before it is passed, because the evaluation order of arguments is
   unspecified. *)
let bound ctx env gen prefix var_ty =
  let value = gen.expr env var_ty in
  { Stress.var = fresh ctx prefix; var_ty; value }
;;

let unboxed_shape ctx =
  let numbers =
    if on "numbers"
    then List.map (fun number -> Unboxed number) unboxed_numbers
    else [ unboxed_float ]
  in
  pick
    ctx
    ([ Any { all_types with only = Some numbers } ]
     @ (if on "utuples" then [ UTuple_of [ Any all_types; Any all_types ] ] else [])
     @ if on "or_null" then [ Or_null_of (Any value_types) ] else [])
;;

(* Most types are values, where these forms show little. At a value type
   [form] builds an unboxed value instead, and a branch on its printed form
   makes a wrong one change the output. *)
let at_unboxed form ctx env ty gen =
  if restricted ty
  then form ctx env ty gen
  else (
    let var = fresh ctx "u" in
    let unboxed_ty = draw_ty ctx (unboxed_shape ctx) in
    let value = form ctx env unboxed_ty gen in
    let env = bind env var unboxed_ty in
    let body = gen.expr env ty in
    if !checks_on
    then (
      let other = gen.expr env ty in
      [%string
        "(let %{var} : %{unboxed_ty#Ty} = %{value} in if Hashtbl.hash (%{printer \
         unboxed_ty} %{var}) land 1 = 0 then %{body} else %{other})"])
    else [%string "(let %{var} : %{unboxed_ty#Ty} = %{value} in %{body})"])
;;

let kinded_identity ctx env ty gen =
  let fn = fresh ctx "id" in
  let attr = pick ctx [ "[@inline never]"; ""; "[@inline]" ] in
  let arg = gen.expr env ty in
  let type_param = ox_syntax [%string "(type a : %{kind ctx ty})"] "(type a)" in
  [%string "(let%{attr} %{fn} %{type_param} (x : a) : a = x in %{fn} %{arg})"]
;;

(* A function whose argument and result have kinds of their own. *)
let kinded_application ctx env ty gen =
  let fn = fresh ctx "app" in
  let param = fresh ctx "p" in
  let param_ty, arg = gen.of_shape env (Any all_types) in
  let body = gen.expr (bind (closure env) param param_ty) ty in
  let type_params =
    ox_syntax
      [%string "(type (a : %{kind ctx param_ty}) (b : %{kind ctx ty}))"]
      "(type a b)"
  in
  [%string
    "(let[@inline never] %{fn} %{type_params} (f : a -> b) (x : a) : b = f x in %{fn} \
     (fun (%{param} : %{param_ty#Ty}) -> %{body}) %{arg})"]
;;

(* A record type whose parameter has [ty]'s kind, written to and read back. *)
let kinded_record ctx env ty gen =
  let module_ = fresh ctx "L" in
  let record = fresh ctx "b" in
  let first = gen.expr env ty in
  let overwrite = gen.expr env Bool in
  let second = gen.expr env ty in
  let type_param = ox_syntax [%string "('a : %{kind ctx ty})"] "'a" in
  [%string
    "(let module %{module_} = struct type %{type_param} box = { mutable contents : 'a; \
     count : int } end in let %{record} : %{ty#Ty} %{module_}.box = { \
     %{module_}.contents = %{first}; count = 0 } in (if %{overwrite} then \
     %{record}.%{module_}.contents <- %{second}); %{record}.%{module_}.contents)"]
;;

(* A signature that hides [ty] and keeps only its kind. *)
let abstract_type ctx env ty gen =
  let module_ = fresh ctx "Ab" in
  let attr = pick ctx [ ""; "[@inline never]" ] in
  let value = gen.expr env ty in
  [%string
    "(let module %{module_} : sig type t%{of_kind ctx ty} val hide : %{ty#Ty} -> t val \
     show : t -> %{ty#Ty} end = struct type t = %{ty#Ty} let%{attr} hide (x : %{ty#Ty}) \
     : t = x let%{attr} show (x : t) : %{ty#Ty} = x end in %{module_}.show \
     (%{module_}.hide %{value}))"]
;;

let kinded_functor ctx env ty gen =
  let functor_ = fresh ctx "Fn" in
  let arg_module = fresh ctx "X" in
  let instance = fresh ctx "M" in
  let condition = bound ctx env gen "c" Bool in
  let first = bound ctx env gen "a" ty in
  let second = bound ctx env gen "a" ty in
  let args = [ condition; first; second ] in
  [%string
    "(let module %{functor_} (%{arg_module} : sig type t%{of_kind ctx ty} val choose : \
     bool -> t -> t -> t end) = struct let[@inline never] run c a b = \
     %{arg_module}.choose c a b end in let module %{instance} = %{functor_} (struct type \
     t = %{ty#Ty} let choose c (a : t) (b : t) = if c then a else b end) in \
     %{Stress.lets args}%{instance}.run %{String.concat \" \" (Stress.names args)})"]
;;

(* A type that [@@unboxed] gives the layout of its only field. *)
let unboxed_wrapper ctx env ty gen =
  let module_ = fresh ctx "U" in
  let as_record = flip ctx in
  let value = gen.expr env ty in
  let declaration, wrap, unwrap =
    if as_record
    then [%string "{ only : %{ty#Ty} }"], "{ only = x }", "x.only"
    else [%string "Only of %{ty#Ty}"], "Only x", "(match x with Only y -> y)"
  in
  [%string
    "(let module %{module_} = struct type t = %{declaration} [@@unboxed] let[@inline \
     never] wrap (x : %{ty#Ty}) : t = %{wrap} let[@inline never] unwrap (x : t) : \
     %{ty#Ty} = %{unwrap} end in %{module_}.unwrap (%{module_}.wrap %{value}))"]
;;

(* Lists, options and tuples accept unboxed elements. The standard library's
   functions on them take only values, so each is read by matching. *)
let in_list ctx env ty gen =
  let nth = fresh ctx "nth" in
  let first = bound ctx env gen "e" ty in
  let second = bound ctx env gen "e" ty in
  let default = bound ctx env gen "e" ty in
  let index = gen.expr env Int in
  [%string
    "(let rec %{nth} (l : %{ty#Ty} list) (n : int) (d : %{ty#Ty}) : %{ty#Ty} = match l \
     with [] -> d | x :: rest -> if n = 0 then x else %{nth} rest (n - 1) d in \
     %{Stress.lets [ first; second; default ]}%{nth} [ %{first.var}; %{second.var} ] \
     (%{index} land 3) %{default.var})"]
;;

let in_option ctx env ty gen =
  let some = fresh ctx "some" in
  let value = gen.expr env ty in
  let default = gen.expr env ty in
  [%string
    "(let[@inline never] %{some} (x : %{ty#Ty}) = Some x in match %{some} %{value} with \
     Some x -> x | None -> %{default})"]
;;

let in_ref ctx env ty gen =
  let cell = fresh ctx "r" in
  let first = gen.expr env ty in
  let overwrite = gen.expr env Bool in
  let second = gen.expr env ty in
  [%string
    "(let %{cell} = ref %{first} in (if %{overwrite} then %{cell} := %{second}); \
     !%{cell})"]
;;

let in_tuple ctx env ty gen =
  let pair = fresh ctx "pair" in
  let value = gen.expr env ty in
  let other_ty, other = gen.of_shape env (Any value_types) in
  [%string
    "(let[@inline never] %{pair} (x : %{ty#Ty}) (y : %{other_ty#Ty}) = x, y in match \
     %{pair} %{value} %{other} with x, _ -> x)"]
;;

(* A match on unboxed integer literals. The scrutinee is masked so that every
   arm can be taken. *)
let literal_match ctx env ty gen =
  let number = pick ctx [ UInt64; UInt32; UNativeint; UInt ] in
  let suffix =
    match number with
    | UInt64 -> "L"
    | UInt32 -> "l"
    | UNativeint -> "n"
    | _ -> ox_syntax "m" ""
  in
  let literal n = ox_syntax "#" "" ^ string_of_int n ^ suffix in
  let scrutinee = gen.expr env (Unboxed number) in
  let zero = gen.expr env ty in
  let one = gen.expr env ty in
  let other = gen.expr env ty in
  [%string
    "(match %{num_module (Unboxed number)}.logand %{scrutinee} %{literal 3} with \
     %{literal 0} -> %{zero} | %{literal 1} -> %{one} | _ -> %{other})"]
;;

(* Enough parameters of any layout that some may not fit in registers.
   Arguments are let-bound because their evaluation order is unspecified. *)
let many_args ctx env ty gen =
  let fn = fresh ctx "wide" in
  let args = Stress.bindings ctx gen env (int_in ctx 6 10) all_types (fun _ -> "k") in
  let params = List.map (fun arg -> fresh ctx "a", arg.Stress.var_ty) args in
  let body = gen.expr (bind_all (closure env) params) ty in
  let param_decls =
    String.concat
      " "
      (List.map (fun (param, param_ty) -> [%string "(%{param} : %{param_ty#Ty})"]) params)
  in
  let arg_names = String.concat " " (Stress.names args) in
  [%string
    "(let[@inline never] %{fn} %{param_decls} : %{ty#Ty} = %{body} in %{Stress.lets \
     args}%{fn} %{arg_names})"]
;;

(* A labeled argument and an optional one, which is passed in an option
   whatever its layout. *)
let labeled_args ctx env ty gen =
  let fn = fresh ctx "lab" in
  let label = fresh ctx "l" in
  let optional = fresh ctx "o" in
  let label_ty, label_arg = gen.of_shape env (Any all_types) in
  let optional_ty = any_type ctx in
  let default = Literal.literal ctx optional_ty in
  let body =
    gen.expr (bind (bind (closure env) label label_ty) optional optional_ty) ty
  in
  let passed = flip ctx in
  let optional_arg =
    if passed then [%string " ~%{optional}:%{gen.expr env optional_ty}"] else ""
  in
  [%string
    "(let[@inline never] %{fn} ~(%{label} : %{label_ty#Ty}) ?(%{optional} = (%{default} \
     : %{optional_ty#Ty})) () : %{ty#Ty} = %{body} in %{fn} \
     ~%{label}:%{label_arg}%{optional_arg} ())"]
;;

let forms ctx env ty gen =
  if !ox_mode && on "layouts"
  then (
    let in_containers = has "unboxed_elements" in
    boost
      (List.map
         (fun form () -> form ctx env ty gen)
         (List.map
            at_unboxed
            ([ kinded_identity
             ; kinded_application
             ; kinded_record
             ; abstract_type
             ; kinded_functor
             ; unboxed_wrapper
             ]
             @ if in_containers then [ in_list; in_option; in_ref; in_tuple ] else [])
          @ [ many_args ]
          @ (if in_containers then [ labeled_args ] else [])
          @ if on "numbers" then [ literal_match ] else [])))
  else []
;;
