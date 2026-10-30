(* Generates well-typed OCaml programs that terminate and whose output does
   not depend on evaluation order or on any unspecified behaviour. *)

open Config
open Ty
open Printer
open Prelude
open Ctx
open Gen_ty
open Literal
open Pattern
open Env
open Forms
open Expr

let module_boundary = "(* module boundary *)\n"

let program ?(ox = false) ?(effect_syntax = false) tc =
  let ctx = { tc; next = 0; decls = [||]; effects = []; used = Hashtbl.create 64 } in
  ox_mode := ox;
  poly_parent := [];
  let forced =
    Option.fold
      ~none:[]
      ~some:(String.split_on_char ',')
      (Sys.getenv_opt "FUZZYCAML_FEATURES")
  in
  features := List.filter (fun f -> Trace.bool tc || List.mem f forced) all_features;
  use_effect_syntax := effect_syntax;
  mixed := [||];
  urec := [||];
  twins := [];
  convs := [];
  let enabled = String.concat " " !features in
  let head = [%string "(* features: %{enabled} *)\n%{prelude ()}"] in
  let buf = Buffer.create 1024 in
  let add decl =
    let i = Array.length ctx.decls in
    ctx.decls <- Array.append ctx.decls [| decl |];
    mixed
    := Array.append
         !mixed
         [| (match decl with
             | Record fields -> List.exists (fun (_, t, _) -> has_float_u t) fields
             | URecord _ -> true
             | Variant constrs ->
               List.exists (fun (_, args) -> List.exists has_float_u args) constrs)
         |];
    urec
    := Array.append
         !urec
         [| (match decl with
             | URecord _ -> true
             | _ -> false)
         |];
    let parent =
      Option.map
        (fun j ->
           match ctx.decls.(j) with
           | Variant cs -> j, cs
           | Record _ | URecord _ -> assert false)
        (List.assoc_opt i !poly_parent)
    in
    Buffer.add_string buf (declaration ?parent i decl);
    i
  in
  let urecords = ox && on "urecords" in
  ignore
  @@ repeat ctx 0 4 (fun _ ->
    let decl = gen_decl ctx in
    let i = add decl in
    (match decl with
     | Record fields when urecords && flip ctx ->
       let u = add (URecord (List.map (fun (f, t, _) -> "u" ^ f, t) fields)) in
       twins := (i, u) :: !twins
     | _ -> ());
    if urecords && flip ~p:0.3 ctx
    then
      ignore
        (add
           (URecord
              (List.init (int_in ctx 1 3) (fun _ ->
                 ( fresh ctx "uf"
                 , match gen_ty ~unboxed:true ctx ~first_order:false 1 with
                   | Or_null _ -> Int
                   | t -> t ))))));
  let depth = int_in ctx 2 7 in
  if (not ox) && on "effects"
  then
    ctx.effects
    <- repeat ctx 1 3 (fun _ ->
         let c = fresh ctx "E" in
         let base () =
           choose ctx [ (fun () -> Int); (fun () -> Bool); (fun () -> fo_ty ctx) ]
         in
         let a = base () in
         let r = base () in
         Buffer.add_string
           buf
           [%string "type _ Effect.t += %{c} : %{a#Ty} -> %{r#Ty} Effect.t\n"];
         c, a, r);
  let env =
    ref { vars = []; locals = []; in_try = false; effs = []; muts = []; in_fun = false }
  in
  let globals =
    List.init
      (if on "atomics" then int_in ctx 0 2 else 0)
      (fun _ ->
         let g = fresh ctx "g" in
         let ty = if flip ctx then Bool else Int in
         Buffer.add_string
           buf
           [%string "let %{g} : %{ty#Ty} Atomic.t = Atomic.make %{literal ctx ty}\n"];
         env := bind !env [%string "(Atomic.get %{g})"] ty;
         g, ty)
  in
  let statement () =
    match globals with
    | [] -> ()
    | _ ->
      let g, ty = pick ctx globals in
      let e env t = expr ctx env t (depth - 1) in
      Buffer.add_string
        buf
        [%string
          "let () = %{atomic_op ctx !env g ty e}\n\
           let () = print_endline (%{printer ty} (Atomic.get %{g}))\n"]
  in
  let binding_ty () =
    match !poly_parent with
    | (child, _) :: _ when flip ctx -> Named child
    | _ -> fo_ty ctx
  in
  (* For the lift pass: the type choices of a binding, under this program's
     features and declarations. *)
  let state = !features, !mixed, !urec, !poly_parent in
  (Trace.binding_types
   := fun target ->
        let saved = !features, !mixed, !urec, !poly_parent, !ox_mode in
        let f, m, u, pp = state in
        features := f;
        mixed := m;
        urec := u;
        poly_parent := pp;
        ox_mode := ox;
        let r = Trace.search binding_ty target in
        let f, m, u, pp, o = saved in
        features := f;
        mixed := m;
        urec := u;
        poly_parent := pp;
        ox_mode := o;
        r);
  let boundary = ref (not (on "modules")) in
  ignore
  @@ repeat ctx 1 6 (fun _ ->
    if (not !boundary) && flip ~p:0.3 ctx
    then (
      boundary := true;
      Buffer.add_string buf module_boundary);
    if flip ~p:0.4 ctx then statement ();
    let ty_start = !Trace.count in
    let ty = binding_ty () in
    let start = !Trace.count in
    let rhs = expr ctx !env ty depth in
    Trace.bindings := (ty_start, start, !Trace.count, ty) :: !Trace.bindings;
    let v = fresh ctx "v" in
    Buffer.add_string
      buf
      [%string
        "let %{v} : %{ty#Ty} = %{rhs}\nlet () = print_endline (%{printer ty} %{v})\n"];
    env := bind !env v ty);
  let conversions =
    String.concat
      ""
      (List.rev_map
         (fun (name, (a, b)) ->
            [%string
              "external %{name} : %{a#Ty} -> %{b#Ty} = \"%%{num_name b}_of_%{num_name a}\"\n"])
         !convs)
  in
  if on "effargs"
  then Buffer.add_string buf "let () = print_endline (string_of_int !ticks)\n";
  head ^ conversions ^ Buffer.contents buf
;;
