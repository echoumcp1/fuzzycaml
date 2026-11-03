open Hegel
open Backend
open Exec
open Toggles
open Known

let cases = ref 0
let compiled = ref 0
let timeouts = ref 0
let known = ref 0

(* One exception per kind of failure, so that Hegel tells them apart without
   backtraces and never shrinks one kind into another. *)
exception Not_compiled of string
exception Backend_crashed of string
exception Backends_disagree of string

let () =
  Printexc.register_printer (function
    | Not_compiled t | Backend_crashed t | Backends_disagree t -> Some t
    | _ -> None)
;;

(* Different choices often give the same program; it is compiled once. Only
   outcomes that are a property of the program are kept: failures and
   rejections, not errors of the machine. *)
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
    raise
      (Not_compiled
         ((if List.exists (compile_error (fun msg -> contains msg "Fatal error")) results
           then "compiler crash: no backend compiled the program\n"
           else "generator bug: no backend compiled the program\n")
          ^ report backends results)));
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
  | Some (Some (e, bt)) -> Printexc.raise_with_backtrace e bt
  | None ->
    (match check_source ~ox tc backends source with
     | () -> Hashtbl.add outcomes key None
     | exception
         (( Not_compiled _
          | Backend_crashed _
          | Backends_disagree _
          | Internal.Assume_rejected ) as e) ->
       let bt = Printexc.get_raw_backtrace () in
       Hashtbl.add outcomes key (Some (e, bt));
       Printexc.raise_with_backtrace e bt)
;;
