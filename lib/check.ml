open Hegel
open Backend
open Exec
open Toggles
open Known

let cases = ref 0
let timeouts = ref 0
let known = ref 0

(* After the first failure, only the reference and the first differing backend
   are run, to make shrinking faster. *)
let focus = ref None

let fail backends results msg =
  let text = msg ^ report backends results in
  if !focus = None
  then (
    prerr_endline text;
    let reference = observable (List.hd results) in
    let odd = List.find_index (fun r -> observable r <> reference) results in
    focus := Some (0 :: Option.to_list odd));
  failwith text
;;

(* All of a test case's draws: the toggled flags, then the program. *)
let generate ~ox ~effect_syntax backends tc =
  let backends = if ox then with_toggles tc backends else backends in
  backends, Program.program ~ox ~effect_syntax tc
;;

let check_case ~size ~ox ~effect_syntax backends tc =
  let backends =
    match !focus with
    | None -> backends
    | Some keep -> List.filteri (fun i _ -> List.mem i keep) backends
  in
  incr cases;
  let backends, source = generate ~ox ~effect_syntax backends tc in
  size := String.length source;
  note tc source;
  (* -dcmm-invariants rejects calls that return unboxed tuples or records. *)
  let backends =
    if ox && (contains source "#(" || contains source "#{")
    then
      List.map
        (fun b -> { b with argv = List.filter (( <> ) "-dcmm-invariants") b.argv })
        backends
    else backends
  in
  (* Trunk -linscan miscompiles native atomics (see [known_bug]), so they are
     replaced with ordinary functions. *)
  let source_for b source =
    if String.ends_with ~suffix:"linscan" b.name && contains source "Atomic."
    then atomic_shim ^ source
    else source
  in
  let results = run_all ~source_for backends source in
  let compile_error f = function
    | Compile_error msg -> f msg
    | Ran _ -> false
  in
  if List.for_all (compile_error (Fun.const true)) results
  then (
    if List.for_all (compile_error known_compile_crash) results
    then (
      incr known;
      assume tc false);
    failwith
      ((if List.exists (compile_error (fun msg -> contains msg "Fatal error")) results
        then "compiler crash: no backend compiled the program\n"
        else "generator bug: no backend compiled the program\n")
       ^ report backends results));
  if
    List.exists
      (function
        | Ran (Timeout, _, _) -> true
        | _ -> false)
      results
  then (
    incr timeouts;
    assume tc false);
  if known_bug backends results source
  then (
    incr known;
    (* FUZZYCAML_SAVE=dir saves programs that hit known bugs. *)
    Option.iter
      (fun dir ->
         Out_channel.with_open_bin
           (Filename.concat dir [%string "known%{Unix.getpid ()#Int}-%{!known#Int}.ml"])
           (fun oc -> output_string oc source))
      (Sys.getenv_opt "FUZZYCAML_SAVE");
    assume tc false);
  (* Programs only raise Exit, so a crash or any other uncaught exception is a
     failure even if all backends agree. *)
  if
    List.exists
      (function
        | Ran (Signaled _, _, _) -> true
        | Ran (Exited 2, _, err) ->
          (* contains, since the debug runtime prints a banner first *)
          not (contains err "Fatal error: exception Stdlib.Exit")
        | _ -> false)
      results
  then fail backends results "backend crashed\n";
  match List.map observable results with
  | first :: rest when List.for_all (( = ) first) rest -> ()
  | _ -> fail backends results "backends disagree\n"
;;

(* Records the choices of each test case, and keeps those of a failing one for
   the lift pass. *)
let check ~ox ~effect_syntax backends tc =
  Trace.reset ();
  let size = ref 0 in
  try check_case ~size ~ox ~effect_syntax backends tc with
  | Failure _ as e ->
    Trace.save !size;
    raise e
;;
