open Config
open Ty
open Printer
open Prelude
open Ctx
open Gen_ty
open Literal
open Pattern
open Env
open Expr

let module_boundary = "(* module boundary *)\n"

(* The items in order, without the declarations no later item or EMI
   replacement mentions. *)
let assemble items =
  let replacements =
    List.map (fun (region : Emi.region) -> region.replacement) !Emi.regions
  in
  let rec keep = function
    | [] -> []
    | (names, text) :: rest ->
      let rest = keep rest in
      let used name =
        List.exists (fun (_, text) -> Text.mentions text name) rest
        || List.exists (fun text -> Text.mentions text name) replacements
      in
      if names <> [] && not (List.exists used names) then rest else (names, text) :: rest
  in
  String.concat "" (List.map snd (keep items))
;;

let decl_names index decl =
  let without_backquote name =
    if name.[0] = '`' then String.sub name 1 (String.length name - 1) else name
  in
  [%string "t%{index#Int}"]
  ::
  (match decl with
   | Record fields -> List.map (fun field -> field.name) fields
   | URecord fields -> List.map fst fields
   | Variant constructors ->
     List.map (fun (constructor, _) -> without_backquote constructor) constructors)
;;

let new_ctx tc = { tc; next = 0; decls = [||]; effects = []; used = Hashtbl.create 64 }

(* Clears the state of the previous program and draws which features this one
   uses. *)
let start_program ~ox ~effect_syntax tc =
  if not (Draw.replaying ()) then Draw.recorded := [];
  if not !erase then Emi.regions := [];
  ox_mode := ox;
  extended_variants := [];
  let forced =
    Option.fold
      ~none:[]
      ~some:(String.split_on_char ',')
      (Sys.getenv_opt "FUZZYCAML_FEATURES")
  in
  features := List.filter (fun f -> Draw.bool tc || List.mem f forced) all_features;
  effect_syntax_on := effect_syntax;
  not_first_order_decls := [||];
  unboxed_record_decls := [||];
  unboxed_twins := [];
  conversions := [];
  inline_records := []
;;

(* The program's top-level items in reverse order, each with the names it
   declares, so that [assemble] can drop the ones nothing uses. *)
type items = { mutable items : (string list * string) list }

let add_item items ?(names = []) text = items.items <- (names, text) :: items.items

let declare ctx items decl =
  let index = Array.length ctx.decls in
  ctx.decls <- Array.append ctx.decls [| decl |];
  not_first_order_decls
  := Array.append
       !not_first_order_decls
       [| (match decl with
           | Record fields -> List.exists (fun field -> has_unboxed field.ty) fields
           | URecord _ -> true
           | Variant constructors ->
             List.exists (fun (_, args) -> List.exists has_unboxed args) constructors)
       |];
  unboxed_record_decls
  := Array.append
       !unboxed_record_decls
       [| (match decl with
           | URecord _ -> true
           | _ -> false)
       |];
  let parent =
    Option.map
      (fun parent ->
         match ctx.decls.(parent) with
         | Variant constructors -> parent, constructors
         | Record _ | URecord _ -> assert false)
      (List.assoc_opt index !extended_variants)
  in
  add_item items ~names:(decl_names index decl) (declaration ?parent index decl);
  index
;;

let declare_types ctx items ~ox =
  let urecords = ox && on "urecords" in
  ignore
  @@ repeat ctx 0 4 (fun _ ->
    let decl = gen_decl ctx in
    let index = declare ctx items decl in
    (match decl with
     | Record fields when urecords && flip ctx ->
       let unboxed =
         declare
           ctx
           items
           (URecord (List.map (fun field -> "u" ^ field.name, field.ty) fields))
       in
       unboxed_twins := (index, unboxed) :: !unboxed_twins
     | _ -> ());
    if urecords && flip ~p:0.3 ctx
    then
      ignore
        (declare
           ctx
           items
           (URecord
              (List.init (int_in ctx 1 3) (fun _ ->
                 ( fresh ctx "uf"
                 , match decode ctx { all_types with depth = 1 } with
                   | Or_null _ -> Int
                   | field_ty -> field_ty ))))))
;;

(* Callbacks the runtime runs at allocations and major cycles, including in the
   middle of an effect operation. They grow the current stack and change
   nothing. Memprof fails on 5.0 to 5.2. *)
let interrupt_callbacks ctx items =
  let depth = pick ctx [ 10; 1000; 100000 ] in
  add_item
    items
    [%string
      "let rec interrupt n = if n = 0 then 0 else 1 + interrupt (n - 1)\n\
       let interrupt () = ignore (Sys.opaque_identity (interrupt %{depth#Int}))\n"];
  if flip ctx
  then (
    let rate = pick ctx [ "0.001"; "0.01"; "0.1"; "1." ] in
    let tracker =
      "{ Gc.Memprof.null_tracker with alloc_minor = (fun _ -> interrupt (); None); \
       alloc_major = (fun _ -> interrupt (); None) }"
    in
    add_item
      items
      [%string
        "let () = try ignore (Gc.Memprof.start ~sampling_rate:%{rate} %{tracker}) with \
         Failure _ -> ()\n"]);
  if flip ctx then add_item items "let () = ignore (Gc.create_alarm interrupt)\n"
;;

let declare_effects ctx items =
  ctx.effects
  <- repeat ctx 1 3 (fun _ ->
       let constructor = fresh ctx "E" in
       let base () =
         choose
           ctx
           [ (fun () -> Int); (fun () -> Bool); (fun () -> first_order_type ctx) ]
       in
       let arg = base () in
       let result = base () in
       add_item
         items
         ~names:[ constructor ]
         [%string
           "type _ Effect.t += %{constructor} : %{arg#Ty} -> %{result#Ty} Effect.t\n"];
       { constructor; arg; result })
;;

(* Global atomics, which statements between the top-level values update. *)
let atomic_globals ctx items env =
  List.init
    (if on "atomics" then int_in ctx 0 2 else 0)
    (fun _ ->
       let global = fresh ctx "g" in
       let ty = if flip ctx then Bool else Int in
       add_item
         items
         ~names:[ global ]
         [%string "let %{global} : %{ty#Ty} Atomic.t = Atomic.make %{literal ctx ty}\n"];
       env := bind !env [%string "(Atomic.get %{global})"] ty;
       global, ty)
;;

(* The functions that [Ty.convert] names. A conversion between two of these
   types is in the module of the earlier one. *)
let conversion_definitions () =
  let stdlib_order = [ Int64; Num Nat; Num I32; Float; Int ] in
  let index ty = Option.get (List.find_index (( = ) ty) stdlib_order) in
  String.concat
    ""
    (List.rev_map
       (fun (name, (from_ty, to_ty)) ->
          let from_ty, to_ty =
            if !erase then boxed_of from_ty, boxed_of to_ty else from_ty, to_ty
          in
          if from_ty = to_ty
          then [%string "let %{name} (x : %{from_ty#Ty}) = x\n"]
          else if !erase && List.mem from_ty stdlib_order && List.mem to_ty stdlib_order
          then (
            (* Upstream has no primitives named like these, so the erased version
               converts through the standard library. *)
            let module_of ty = String.capitalize_ascii (num_name ty) in
            let fn =
              if index from_ty < index to_ty
              then module_of from_ty ^ ".to_" ^ num_name to_ty
              else module_of to_ty ^ ".of_" ^ num_name from_ty
            in
            [%string "let %{name} (x : %{from_ty#Ty}) : %{to_ty#Ty} = %{fn} x\n"])
          else
            [%string
              "external %{name} : %{from_ty#Ty} -> %{to_ty#Ty} = \"%%{num_name \
               to_ty}_of_%{num_name from_ty}\"\n"])
       !conversions)
;;

let program ?(ox = false) ?(effect_syntax = false) tc =
  let ctx = new_ctx tc in
  start_program ~ox ~effect_syntax tc;
  let enabled = String.concat " " !features in
  let head = [%string "(* features: %{enabled} *)\n%{prelude ()}"] in
  let items = { items = [] } in
  declare_types ctx items ~ox;
  if on "interrupts" then interrupt_callbacks ctx items;
  let depth = int_in ctx 2 7 in
  if on "effects" then declare_effects ctx items;
  let env =
    ref
      { vars = []
      ; locals = []
      ; in_try = false
      ; escapes = false
      ; handled_effects = []
      ; mutables = []
      ; in_fun = false
      }
  in
  let globals = atomic_globals ctx items env in
  let update_a_global () =
    match globals with
    | [] -> ()
    | _ ->
      let global, ty = pick ctx globals in
      let expr = (gen ctx (depth - 1)).expr in
      add_item
        items
        [%string
          "let () = %{Atomics.atomic_op ctx !env global ty expr}\n\
           let () = print_endline (%{printer ty} (Atomic.get %{global}))\n"]
  in
  let gen = gen ctx depth in
  let upcast_candidates =
    match !extended_variants with
    | (child, _) :: _ -> [ Named child ]
    | [] -> []
  in
  let split = ref (not (on "modules")) in
  ignore
  @@ repeat ctx 1 6 (fun _ ->
    if flip ~p:(if !split then 0. else 0.3) ctx
    then (
      split := true;
      add_item items module_boundary);
    if flip ~p:0.4 ctx then update_a_global ();
    let escapes = on "escapes" && flip ctx in
    let ty, rhs =
      gen.of_shape
        ~candidates:upcast_candidates
        ~p:0.5
        { !env with escapes }
        (Any first_order_types)
    in
    let rhs =
      if escapes then [%string "(try %{rhs} with Exit -> %{literal ctx ty})"] else rhs
    in
    let var = fresh ctx "v" in
    add_item
      items
      [%string
        "let %{var} : %{ty#Ty} = %{rhs}\nlet () = print_endline (%{printer ty} %{var})\n"];
    env := bind !env var ty);
  (* Interrupt callbacks allocate, which a zero_alloc test would see. *)
  if !props && not (on "interrupts")
  then ignore @@ repeat ctx 0 2 (fun _ -> add_item items (Zero_alloc.test ctx !env gen));
  if on "effargs" then add_item items "let () = print_endline (string_of_int !ticks)\n";
  if on "observe" then add_item items "let () = print_endline (string_of_int !obs)\n";
  head ^ conversion_definitions () ^ assemble (List.rev items.items)
;;

(* The erased version is also compiled without optimization hints, as a
   reference that the optimizer has little to work with. *)
let unhinted =
  Markers.without_all
    [ "[@inline never]"
    ; "[@inline always]"
    ; "[@inline]"
    ; "[@inlined never]"
    ; "[@inlined]"
    ; "[@specialise]"
    ; "[@unrolled 2]"
    ; "[@loop always]"
    ; "[@tail_mod_cons]"
    ; "[@tailcall false]"
    ]
;;

(* The last program generated again with the same choices, erased, without its
   wrappers or optimization hints. *)
let erased ~ox ~effect_syntax tc =
  Draw.replay (fun () ->
    erase := true;
    Fun.protect
      ~finally:(fun () -> erase := false)
      (fun () -> unhinted (Markers.without_wrappers (program ~ox ~effect_syntax tc))))
;;
