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

let mentions text name =
  let n = String.length name in
  let alnum c =
    (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
  in
  let rec go i =
    i + n <= String.length text
    && ((String.sub text i n = name
         && (i = 0 || not (alnum text.[i - 1]))
         && (i + n = String.length text || not (alnum text.[i + n])))
        || go (i + 1))
  in
  go 0
;;

let assemble pieces =
  let rec keep = function
    | [] -> []
    | (names, text) :: rest ->
      let rest = keep rest in
      if
        names <> []
        && not
             (List.exists (fun n -> List.exists (fun (_, t) -> mentions t n) rest) names)
      then rest
      else (names, text) :: rest
  in
  String.concat "" (List.map snd (keep pieces))
;;

let decl_names i decl =
  let strip c = if c.[0] = '`' then String.sub c 1 (String.length c - 1) else c in
  [%string "t%{i#Int}"]
  ::
  (match decl with
   | Record fields -> List.map (fun (f, _, _) -> f) fields
   | URecord fields -> List.map fst fields
   | Variant constrs -> List.map (fun (c, _) -> strip c) constrs)
;;

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
  features := List.filter (fun f -> Draw.bool tc || List.mem f forced) all_features;
  use_effect_syntax := effect_syntax;
  mixed := [||];
  urec := [||];
  twins := [];
  convs := [];
  let enabled = String.concat " " !features in
  let head = [%string "(* features: %{enabled} *)\n%{prelude ()}"] in
  let pieces = ref [] in
  let piece ?(names = []) text = pieces := (names, text) :: !pieces in
  let add decl =
    let i = Array.length ctx.decls in
    ctx.decls <- Array.append ctx.decls [| decl |];
    mixed
    := Array.append
         !mixed
         [| (match decl with
             | Record fields ->
               List.exists (fun (_, field_ty, _) -> has_float_u field_ty) fields
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
    piece ~names:(decl_names i decl) (declaration ?parent i decl);
    i
  in
  let urecords = ox && on "urecords" in
  ignore
  @@ repeat ctx 0 4 (fun _ ->
    let decl = gen_decl ctx in
    let i = add decl in
    (match decl with
     | Record fields when urecords && flip ctx ->
       let unboxed =
         add
           (URecord (List.map (fun (field, field_ty, _) -> "u" ^ field, field_ty) fields))
       in
       twins := (i, unboxed) :: !twins
     | _ -> ());
    if urecords && flip ~p:0.3 ctx
    then
      ignore
        (add
           (URecord
              (List.init (int_in ctx 1 3) (fun _ ->
                 ( fresh ctx "uf"
                 , match decode ctx { top with depth = 1 } with
                   | Or_null _ -> Int
                   | t -> t ))))));
  let depth = int_in ctx 2 7 in
  if (not ox) && on "effects"
  then
    ctx.effects
    <- repeat ctx 1 3 (fun _ ->
         let con = fresh ctx "E" in
         let base () =
           choose ctx [ (fun () -> Int); (fun () -> Bool); (fun () -> fo_ty ctx) ]
         in
         let arg = base () in
         let result = base () in
         piece
           ~names:[ con ]
           [%string "type _ Effect.t += %{con} : %{arg#Ty} -> %{result#Ty} Effect.t\n"];
         con, arg, result);
  let env =
    ref { vars = []; locals = []; in_try = false; effs = []; muts = []; in_fun = false }
  in
  let globals =
    List.init
      (if on "atomics" then int_in ctx 0 2 else 0)
      (fun _ ->
         let g = fresh ctx "g" in
         let ty = if flip ctx then Bool else Int in
         piece
           ~names:[ g ]
           [%string "let %{g} : %{ty#Ty} Atomic.t = Atomic.make %{literal ctx ty}\n"];
         env := bind !env [%string "(Atomic.get %{g})"] ty;
         g, ty)
  in
  let statement () =
    match globals with
    | [] -> ()
    | _ ->
      let g, ty = pick ctx globals in
      let e = (gen ctx (depth - 1)).e in
      piece
        [%string
          "let () = %{atomic_op ctx !env g ty e}\n\
           let () = print_endline (%{printer ty} (Atomic.get %{g}))\n"]
  in
  let g = gen ctx depth in
  let poly_child =
    match !poly_parent with
    | (child, _) :: _ -> [ Named child ]
    | [] -> []
  in
  let boundary = ref (not (on "modules")) in
  ignore
  @@ repeat ctx 1 6 (fun _ ->
    if flip ~p:(if !boundary then 0. else 0.3) ctx
    then (
      boundary := true;
      piece module_boundary);
    if flip ~p:0.4 ctx then statement ();
    let ty, rhs = g.free ~candidates:poly_child ~p:0.5 !env (Any fo) in
    let v = fresh ctx "v" in
    piece
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
  if on "effargs" then piece "let () = print_endline (string_of_int !ticks)\n";
  head ^ conversions ^ assemble (List.rev !pieces)
;;
