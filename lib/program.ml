(* Generates well-typed OCaml programs that terminate and whose output does
   not depend on evaluation order or on any unspecified behaviour. *)

open Hegel
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
  features := List.filter (fun _ -> draw_silent tc (booleans ())) all_features;
  use_effect_syntax := effect_syntax;
  mixed := [||];
  urec := [||];
  twins := [];
  convs := [];
  let head = p "(* features: %s *)\n%s" (String.concat " " !features) (prelude ()) in
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
    urec := Array.append !urec [| (match decl with URecord _ -> true | _ -> false) |];
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
  ignore @@ repeat ctx 0 4 (fun _ ->
    let decl = gen_decl ctx in
    let i = add decl in
    (match decl with
     | Record fields when urecords && draw_silent ctx.tc (booleans ()) ->
       let u = add (URecord (List.map (fun (f, t, _) -> "u" ^ f, t) fields)) in
       twins := (i, u) :: !twins
     | _ -> ());
    if urecords && draw_silent ctx.tc (booleans ~p:0.3 ())
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
         let base () = choose ctx [ (fun () -> Int); (fun () -> Bool); (fun () -> fo_ty ctx) ] in
         let a = base () in
         let r = base () in
         Buffer.add_string buf (p "type _ Effect.t += %s : %s -> %s Effect.t\n" c (show_ty a) (show_ty r));
         c, a, r);
  let env = ref { vars = []; locals = []; in_try = false; effs = []; muts = [] } in
  let globals =
    List.init (if on "atomics" then int_in ctx 0 2 else 0) (fun _ ->
      let g = fresh ctx "g" in
      let ty = if draw_silent ctx.tc (booleans ()) then Bool else Int in
      Buffer.add_string
        buf
        (p "let %s : %s Atomic.t = Atomic.make %s\n" g (show_ty ty) (literal ctx ty));
      env := bind !env (p "(Atomic.get %s)" g) ty;
      g, ty)
  in
  let statement () =
    match globals with
    | [] -> ()
    | _ ->
      let g, ty = List.nth globals (int_in ctx 0 (List.length globals - 1)) in
      let e env t = expr ctx env t (depth - 1) in
      Buffer.add_string
        buf
        (p
           "let () = %s\nlet () = print_endline (%s (Atomic.get %s))\n"
           (atomic_op ctx !env g ty e)
           (printer ty)
           g)
  in
  let boundary = ref (not (on "modules")) in
  ignore @@ repeat ctx 1 6 (fun _ ->
    if (not !boundary) && draw_silent ctx.tc (booleans ~p:0.3 ())
    then (
      boundary := true;
      Buffer.add_string buf module_boundary);
    if draw_silent ctx.tc (booleans ~p:0.4 ()) then statement ();
    let ty =
      match !poly_parent with
      | (child, _) :: _ when draw_silent ctx.tc (booleans ()) -> Named child
      | _ -> fo_ty ctx
    in
    let v = fresh ctx "v" in
    Buffer.add_string
      buf
      (p
         "let %s : %s = %s\nlet () = print_endline (%s %s)\n"
         v
         (show_ty ty)
         (expr ctx !env ty depth)
         (printer ty)
         v);
    env := bind !env v ty);
  let conversions =
    String.concat
      ""
      (List.rev_map
         (fun (name, (a, b)) ->
            p "external %s : %s -> %s = \"%%%s_of_%s\"\n" name (show_ty a) (show_ty b) (num_name b) (num_name a))
         !convs)
  in
  head ^ conversions ^ Buffer.contents buf
;;
