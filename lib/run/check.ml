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

let () =
  Printexc.register_printer (function
    | Not_compiled t | Backend_crashed t | Backends_disagree t -> Some t
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

let generate ~ox ~effect_syntax backends tc =
  let backends = if ox then with_toggles tc backends else backends in
  backends, Program.program ~ox ~effect_syntax tc
;;

let check_source ~ox tc backends source =
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
    if
      on_trunk b.name
      && String.ends_with ~suffix:"linscan" b.name
      && Text.contains source "Atomic."
    then atomic_shim ^ source
    else source
  in
  let results = run_all ~source_for backends source in
  let compile_error fn = function
    | Compile_error msg -> fn msg
    | Ran _ -> false
  in
  let save kind count why =
    Option.iter
      (fun dir ->
         Out_channel.with_open_bin
           (Filename.concat dir [%string "%{kind}%{Unix.getpid ()#Int}-%{count#Int}.ml"])
           (fun oc ->
              output_string oc [%string "(* %{kind} %{why} *)\n"];
              List.iter
                (fun b ->
                   output_string
                     oc
                     [%string "(* backend %{b.name}: %{String.concat \" \" b.argv} *)\n"])
                backends;
              output_string oc source))
      (Sys.getenv_opt "FUZZYCAML_SAVE")
  in
  let skip_known bug =
    incr known;
    save "known" !known [%string "bug: %{bug}"];
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
  (* Runs [backends] again on the program, edited. *)
  let rerun ~edit backends =
    run_all ~source_for:(fun b source -> edit (source_for b source)) backends source
  in
  Option.iter skip_known (memprof_perform ~rerun backends results source);
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
  match List.map observable results with
  | first :: rest when List.for_all (( = ) first) rest -> ()
  | _ -> fail backends results (fun t -> Backends_disagree t) "backends disagree\n"
;;

let check ~ox ~effect_syntax backends tc =
  incr cases;
  let backends, source = generate ~ox ~effect_syntax backends tc in
  note tc source;
  let key =
    Digest.string (String.concat "\000" (source :: List.map (fun b -> b.name) backends))
  in
  if Hashtbl.length outcomes > 100_000 then Hashtbl.reset outcomes;
  match Hashtbl.find_opt outcomes key with
  | Some None -> ()
  | Some (Some (exn, backtrace)) -> Printexc.raise_with_backtrace exn backtrace
  | None ->
    (match check_source ~ox tc backends source with
     | () -> Hashtbl.add outcomes key None
     | exception
         (( Not_compiled _
          | Backend_crashed _
          | Backends_disagree _
          | Internal.Assume_rejected ) as exn) ->
       let backtrace = Printexc.get_raw_backtrace () in
       Hashtbl.add outcomes key (Some (exn, backtrace));
       Printexc.raise_with_backtrace exn backtrace)
;;
