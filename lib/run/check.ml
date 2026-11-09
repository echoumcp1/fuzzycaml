open Hegel
open Backend
open Exec
open Toggles
open Known

let cases = ref 0
let compiled = ref 0
let timeouts = ref 0
let known = ref 0
let rejected = ref 0

exception Not_compiled of string
exception Backend_crashed of string
exception Backends_disagree of string
exception Property_failed of string

let () =
  Printexc.register_printer (function
    | Not_compiled t | Backend_crashed t | Backends_disagree t | Property_failed t ->
      Some t
    | _ -> None)
;;

let outcomes : (string, (exn * Printexc.raw_backtrace) option) Hashtbl.t =
  Hashtbl.create 1024
;;

(* After the first failure, only the reference and the first differing backend
   are run, to make shrinking faster. *)
let focus = ref None

let fail backends results exn msg =
  let text = msg ^ report backends results in
  if Option.is_none !focus
  then (
    prerr_endline text;
    let reference = observable (List.hd results) in
    let odd = List.find_index (fun r -> observable r <> reference) results in
    focus := Some (0 :: Option.to_list odd));
  raise (exn text)
;;

let name_suffix = function
  | Original -> ""
  | Erased -> " (erased)"
  | Variant -> " (variant)"
  | Emi -> " (emi)"
;;

let compiling version b = { b with name = b.name ^ name_suffix version; version }

(* The versions of a generated program that its source does not hold. The
   erased version is generated separately and the EMI version after a coverage
   run, and both lose the zero_alloc tests the checker rejects. *)
type versions =
  { mutable erased : string
  ; mutable emi : string
  }

(* In props mode, backends other than the toggles one are upstream compilers,
   which check only the erased version, without the modules they lack. *)
let upstream b = !Config.props && not (Text.contains b.name "-toggles")
let ox_modules = [ "F32"; "I8"; "I16" ]

let for_upstream source =
  String.split_on_char '\n' source
  |> List.filter (fun l ->
    not (List.exists (fun m -> String.starts_with ~prefix:("module " ^ m) l) ox_modules))
  |> String.concat "\n"
;;

let generate ~ox ~effect_syntax backends tc =
  let upstreams, backends = List.partition upstream backends in
  let backends = if ox then with_toggles tc backends else backends in
  let source = Program.program ~ox ~effect_syntax tc in
  let versions = { erased = ""; emi = "" } in
  let backends =
    if !Config.props
    then (
      versions.erased <- Program.erased ~ox ~effect_syntax tc;
      let erasing b =
        compiling
          Erased
          { b with
            argv = b.argv @ [ "-extension-universe"; "no_extensions"; "-Oclassic" ]
          }
      in
      let upstreams =
        if List.exists (Text.contains (for_upstream versions.erased)) ox_modules
        then []
        else upstreams
      in
      backends
      @ List.map erasing backends
      @ List.map (compiling Erased) upstreams
      @ (if Markers.has_wrappers source then List.map (compiling Variant) backends else [])
      @ if Emi.has_regions source then List.map (compiling Emi) backends else [])
    else backends
  in
  backends, source, versions
;;

let version_source versions b source =
  match b.version with
  | Original -> if !Config.props then Markers.without_wrappers source else source
  | Variant -> source
  | Erased -> versions.erased
  | Emi -> versions.emi
;;

let check_source ~ox tc backends source versions =
  let backends =
    match !focus with
    | None -> backends
    | Some keep -> List.filteri (fun i _ -> List.mem i keep) backends
  in
  incr compiled;
  (* -dcmm-invariants rejects calls that return unboxed tuples or records. *)
  let backends =
    if ox && (Text.contains source "#(" || Text.contains source "#{")
    then
      List.map
        (fun b -> { b with argv = List.filter (( <> ) "-dcmm-invariants") b.argv })
        backends
    else backends
  in
  let source_for b source =
    let source = version_source versions b source in
    let source = if upstream b then for_upstream source else source in
    if
      on_trunk b.name
      && String.ends_with ~suffix:"linscan" b.name
      && Text.contains source "Atomic."
    then atomic_shim ^ source
    else source
  in
  (* Compiles again without the zero_alloc test whose function the checker
     rejects, if any. *)
  let rec compile source =
    (* The coverage run decides what the EMI version prunes. When it does not
       finish, nothing is pruned. *)
    List.iter
      (fun b ->
         if b.version = Emi
         then (
           let original = Markers.without_wrappers source in
           let hits =
             match run_all [ b ] (Emi.covered original) with
             | [ Ran (Exited (0 | 2), _, err) ] -> Emi.hits err
             | _ -> None
           in
           versions.emi
           <- Option.fold ~none:original ~some:(fun hits -> Emi.pruned hits original) hits;
           note tc ("(* emi *)\n" ^ Markers.clean versions.emi)))
      backends;
    let results = run_all ~source_for backends source in
    let rejected =
      List.find_map
        (function
          | Compile_error msg -> Zero_alloc.rejected msg
          | Ran _ -> None)
        results
    in
    match rejected with
    | Some fn when Text.contains source [%string "(*[%{fn}*)"] ->
      versions.erased <- Zero_alloc.drop fn versions.erased;
      compile (Zero_alloc.drop fn source)
    | _ -> source, results
  in
  let source, results = compile source in
  let compile_error fn = function
    | Compile_error msg -> fn msg
    | Ran _ -> false
  in
  let save ?(source = source) ?(note = "") kind count why =
    Option.iter
      (fun dir ->
         Out_channel.with_open_bin
           (Filename.concat dir [%string "%{kind}%{Unix.getpid ()#Int}-%{count#Int}.ml"])
           (fun oc ->
              output_string oc [%string "(* %{kind} %{why} *)\n%{note}"];
              List.iter
                (fun b ->
                   output_string
                     oc
                     [%string "(* backend %{b.name}: %{String.concat \" \" b.argv} *)\n"])
                backends;
              output_string oc source))
      (Sys.getenv_opt "FUZZYCAML_SAVE")
  in
  let skip_known ?crashed bug =
    incr known;
    (match crashed with
     | None -> save "known" !known [%string "bug: %{bug}"]
     | Some b ->
       (* The version that crashed, since the others may not. *)
       save
         ~source:(source_for b source)
         ~note:[%string "(* crashed: %{b.name} *)\n"]
         "known"
         !known
         [%string "bug: %{bug}"]);
    assume tc false
  in
  (* A program a compiler rejects without crashing is a generator bug. It is
     saved and skipped, so a run goes on. *)
  let reject () =
    incr rejected;
    save
      "rejected"
      !rejected
      (String.map (fun c -> if c = '*' then '#' else c) (report backends results));
    assume tc false
  in
  let crashed msg =
    List.exists (Text.contains msg) [ "Fatal error"; "Assembler error"; "linking" ]
  in
  (* Runs [backends] again on their versions of the program, edited. *)
  let rerun ~edit backends =
    run_all ~source_for:(fun b source -> edit (source_for b source)) backends source
  in
  Option.iter skip_known (memprof_perform ~rerun backends results source);
  (* Versions differ in code, so one of them alone may hit a known crash. *)
  if !Config.props
  then
    Option.iter
      (fun (b, bug) -> skip_known ~crashed:b bug)
      (List.find_map
         (fun (b, result) ->
            Option.map
              (fun bug -> b, bug)
              (match result with
               | Compile_error msg -> known_compile_crash msg
               | Ran (_, _, err) ->
                 if Text.contains err "Dead variable in bound pattern"
                 then Some "reaper: dead variable"
                 else None))
         (List.combine backends results));
  if List.for_all (compile_error (Fun.const true)) results
  then (
    (match
       List.map
         (function
           | Compile_error msg -> known_compile_crash msg
           | Ran _ -> None)
         results
     with
     | Some bug :: rest when List.for_all Option.is_some rest -> skip_known bug
     | _ -> ());
    if not (List.exists (compile_error crashed) results) then reject ();
    raise
      (Not_compiled
         ("compiler crash: no backend compiled the program\n" ^ report backends results)));
  (* In props mode, when one version compiles and another does not, the
     generator rewrote that version wrongly, unless the compiler crashed. *)
  if !Config.props && List.exists (compile_error (fun msg -> not (crashed msg))) results
  then reject ();
  if
    List.exists
      (function
        | Ran (Timeout, _, _) -> true
        | _ -> false)
      results
  then (
    incr timeouts;
    assume tc false);
  Option.iter skip_known (known_bug ~rerun backends results);
  (* Programs only raise Exit, so a crash or any other uncaught exception is a
     failure even if all backends agree. *)
  if
    List.exists
      (function
        | Ran (Signaled _, _, _) -> true
        | Ran (Exited 2, _, err) ->
          (* The debug runtime prints a banner first. *)
          not
            (Text.contains err "Fatal error: exception Stdlib.Exit"
             || Text.contains err "Exception: Stdlib.Exit.")
        | _ -> false)
      results
  then fail backends results (fun t -> Backend_crashed t) "backend crashed\n";
  if
    List.exists
      (function
        | Ran (_, out, _) ->
          String.starts_with ~prefix:Markers.failure out
          || Text.contains out ("\n" ^ Markers.failure)
        | Compile_error _ -> false)
      results
  then fail backends results (fun t -> Property_failed t) "property failed\n";
  match List.map observable results with
  | first :: rest when List.for_all (( = ) first) rest -> ()
  | _ -> fail backends results (fun t -> Backends_disagree t) "backends disagree\n"
;;

let check ~ox ~effect_syntax backends tc =
  incr cases;
  let backends, source, versions = generate ~ox ~effect_syntax backends tc in
  if !Config.props
  then (
    note tc (Markers.clean (Markers.without_wrappers source));
    note tc ("(* erased *)\n" ^ versions.erased);
    if Markers.has_wrappers source then note tc ("(* variant *)\n" ^ Markers.clean source))
  else note tc source;
  let key =
    Digest.string (String.concat "\000" (source :: List.map (fun b -> b.name) backends))
  in
  if Hashtbl.length outcomes > 100_000 then Hashtbl.reset outcomes;
  match Hashtbl.find_opt outcomes key with
  | Some None -> ()
  | Some (Some (exn, backtrace)) -> Printexc.raise_with_backtrace exn backtrace
  | None ->
    (match check_source ~ox tc backends source versions with
     | () -> Hashtbl.add outcomes key None
     | exception
         (( Not_compiled _
          | Backend_crashed _
          | Backends_disagree _
          | Property_failed _
          | Internal.Assume_rejected ) as exn) ->
       let backtrace = Printexc.get_raw_backtrace () in
       Hashtbl.add outcomes key (Some (exn, backtrace));
       Printexc.raise_with_backtrace exn backtrace)
;;
