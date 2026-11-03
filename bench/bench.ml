(* A shrinking benchmark that needs no compiler. A failure is a program whose
   text satisfies an oracle, and the measure is how small the shrunk program
   is by the number of test calls, since a real shrink, where every call
   compiles a program, gets a few hundred of them before Hegel's time limit.

     bench run ORACLE SEED [-o FILE]        shrink one failure
     bench grid OUT [-seeds N] [-jobs J]    every oracle over seeds 1..N
     bench summary OUT...                   medians of the runs in each OUT
     bench compare OLD NEW                  the runs of NEW against those of OLD, seed by seed
     bench show OUT ORACLE SEED             the shrunk program of one run
     bench rate N                           hit rate of each oracle over N programs
     bench compile N                        compile N generated programs with the first backend

   A run writes a summary line, then the improvements as "  compiles size
   seconds", then the shrunk program with "| " before each line. Sizes count the
   characters after the prelude, without the lines that print values; compiles
   count distinct programs after the first failure, which is what a real shrink
   pays for. BENCH_DEBUG=1 prints Hegel's shrinker log and BENCH_DEBUG=2 every
   program tried. *)

open Hegel

let contains s sub = Exec.contains s sub

(* The part of a program the oracle sees: after the prelude, without the
   printing lines, so that a printer's [String.concat] does not count. *)
let body source =
  let prelude = Prelude.prelude () in
  let start =
    match Exec.find source prelude with
    | Some i -> i + String.length prelude
    | None -> 0
  in
  String.sub source start (String.length source - start)
  |> String.split_on_char '\n'
  |> List.filter (fun l -> not (String.starts_with ~prefix:"let () = print_endline" l))
  |> String.concat "\n"
;;

(* Each needs an expression whose type differs from the one around it, or two
   constructs at once, like a compiler bug does. *)
let oracles =
  [ ("shr", fun s -> contains s "Int64.shift_right_logical")
  ; ("sort", fun s -> contains s "List.sort compare")
  ; ("fma", fun s -> contains s "Float.fma")
  ; ("hash_fold", fun s -> contains s "Hashtbl.hash" && contains s "List.fold_left")
  ; ("fst_code", fun s -> contains s "(fst " && contains s "Char.code")
  ; ("perform_lazy", fun s -> contains s "Effect.perform" && contains s "Lazy.force")
  ; ("upd_rem", fun s -> contains s " with f" && contains s "Int64.rem")
  ; ("map_chr", fun s -> contains s "List.map" && contains s "Char.chr")
  ]
;;

let debug = Sys.getenv_opt "BENCH_DEBUG"

let settings seed =
  { (Settings.create ~test_cases:1_000_000 ~seed ()) with
    suppress_health_check =
      Settings.
        [ Filter_too_much; Too_slow; Test_cases_too_large; Large_initial_test_case ]
  ; database = Disabled
  ; verbosity = (if debug <> None then Debug else Quiet)
  ; print_blob = false
  }
;;

let generate tc = Program.program ~effect_syntax:true tc

let rate n =
  let hits = Hashtbl.create 8 in
  let total = ref 0 in
  let sizes = ref 0 in
  (try
     run_hegel_test
       ~settings:{ (settings 1) with phases = [ Generate ] }
       (fun tc ->
          let b = body (generate tc) in
          incr total;
          sizes := !sizes + String.length b;
          List.iter
            (fun (name, f) ->
               if f b
               then
                 Hashtbl.replace
                   hits
                   name
                   (1 + Option.value ~default:0 (Hashtbl.find_opt hits name)))
            oracles;
          if !total >= n then failwith "done")
   with
   | _ -> ());
  Printf.printf "programs %d, mean body size %d\n" !total (!sizes / max 1 !total);
  List.iter
    (fun (name, _) ->
       Printf.printf
         "%-14s %5.1f%%\n"
         name
         (100.
          *. float (Option.value ~default:0 (Hashtbl.find_opt hits name))
          /. float !total))
    oracles
;;

(* improvements as (compiles, size, seconds) *)
let curve = ref []
let calls = ref 0
let compiles = ref 0
let seen = Hashtbl.create 1024
let best = ref max_int
let last = ref 0
let last_body = ref ""
let t0 = ref 0.

let test oracle tc =
  incr calls;
  let src =
    try generate tc with
    | e ->
      if debug = Some "2"
      then Printf.printf "#%d EXN %s\n%!" !calls (Printexc.to_string e);
      raise e
  in
  let b = body src in
  let n = String.length b in
  let fails = oracle b in
  if debug = Some "2"
  then
    Printf.printf
      "#%d %b: %s\n%!"
      !calls
      fails
      (String.concat " " (String.split_on_char '\n' (String.trim b)));
  let key = Digest.string b in
  if !best < max_int && not (Hashtbl.mem seen key)
  then (
    Hashtbl.add seen key ();
    incr compiles);
  if fails
  then (
    last := n;
    last_body := b;
    if n < !best
    then (
      best := n;
      Hashtbl.replace seen key ();
      curve := (!compiles, n, Unix.gettimeofday () -. !t0) :: !curve);
    failwith "oracle")
;;

(* The oracles never compile anything, so a change that drops needed text looks
   like a gain to them; this compiles [n] generated programs with the first
   backend and prints those it rejects. *)
let compile n =
  let backend = List.hd (Backend.discover ~ox:false) in
  let effect_syntax = Backend.effect_syntax ~ox:false [ backend ] in
  Printf.printf "backend %s\n%!" backend.name;
  let bad = ref 0 in
  let total = ref 0 in
  (try
     run_hegel_test
       ~settings:{ (settings 1) with phases = [ Generate ] }
       (fun tc ->
          let src = Program.program ~effect_syntax tc in
          incr total;
          (match Exec.run_all [ backend ] src with
           | [ Exec.Compile_error msg ] ->
             incr bad;
             Printf.printf "--- program %d:\n%s\n%s\n%!" !total (body src) msg
           | _ -> ());
          if !total >= n then failwith "done")
   with
   | _ -> ());
  Printf.printf "%d of %d programs did not compile\n" !bad !total
;;

let checkpoints = [ 100; 300; 1000; 3000 ]

let run name seed out =
  let oracle = List.assoc name oracles in
  t0 := Unix.gettimeofday ();
  (try run_hegel_test ~settings:(settings seed) (test oracle) with
   | _ -> ());
  let curve = List.rev !curve in
  let init =
    match curve with
    | (_, n, _) :: _ -> n
    | [] -> -1
  in
  let at k = List.fold_left (fun acc (c, n, _) -> if c <= k then n else acc) init curve in
  let oc = Option.fold ~none:stdout ~some:open_out out in
  Printf.fprintf
    oc
    "%s %d init %d final %d min %d calls %d compiles %d time %.0f%s\n"
    name
    seed
    init
    !last
    !best
    !calls
    !compiles
    (Unix.gettimeofday () -. !t0)
    (String.concat
       ""
       (List.map (fun k -> Printf.sprintf " at%d %d" k (at k)) checkpoints));
  List.iter (fun (c, n, t) -> Printf.fprintf oc "  %d %d %.1f\n" c n t) curve;
  List.iter
    (fun l -> Printf.fprintf oc "| %s\n" l)
    (String.split_on_char '\n' (String.trim !last_body));
  if out <> None then close_out oc
;;

let load file =
  In_channel.with_open_text file In_channel.input_lines
  |> List.filter_map (fun line ->
    if
      String.starts_with ~prefix:" " line
      || String.starts_with ~prefix:"|" line
      || line = ""
    then None
    else (
      match String.split_on_char ' ' line with
      | name :: seed :: fields ->
        let rec pairs = function
          | k :: v :: rest -> (k, int_of_string v) :: pairs rest
          | _ -> []
        in
        Some (name, int_of_string seed, pairs fields)
      | _ -> None))
;;

let grid out ~seeds ~jobs =
  let exe = Sys.executable_name in
  let todo =
    ref (List.concat_map (fun (o, _) -> List.init seeds (fun s -> o, s + 1)) oracles)
  in
  let running = Hashtbl.create jobs in
  let oc = open_out out in
  let null = Unix.openfile "/dev/null" [ O_WRONLY ] 0 in
  let start (o, s) =
    let file = Filename.temp_file "bench" ".txt" in
    let pid =
      Unix.create_process
        exe
        [| exe; "run"; o; string_of_int s; "-o"; file |]
        Unix.stdin
        null
        null
    in
    Hashtbl.add running pid file
  in
  let finish () =
    let pid, _ = Unix.wait () in
    let file = Hashtbl.find running pid in
    Hashtbl.remove running pid;
    output_string oc (In_channel.with_open_text file In_channel.input_all);
    flush oc;
    Sys.remove file
  in
  while !todo <> [] || Hashtbl.length running > 0 do
    if !todo <> [] && Hashtbl.length running < jobs
    then (
      start (List.hd !todo);
      todo := List.tl !todo)
    else finish ()
  done;
  close_out oc
;;

let median l =
  let a = Array.of_list (List.sort compare l) in
  let n = Array.length a in
  if n = 0
  then nan
  else if n mod 2 = 1
  then float a.(n / 2)
  else float (a.((n / 2) - 1) + a.(n / 2)) /. 2.
;;

let summary files =
  let fields =
    [ "final"; "min"; "calls"; "compiles" ]
    @ List.map (fun k -> Printf.sprintf "at%d" k) checkpoints
  in
  let loaded = List.map (fun f -> f, load f) files in
  let line label n runs =
    Printf.printf
      "%-14s %-16s %4d %s\n"
      label
      n
      (List.length runs)
      (String.concat
         " "
         (List.map
            (fun f ->
               Printf.sprintf
                 "%8.0f"
                 (median (List.map (fun (_, _, kv) -> List.assoc f kv) runs)))
            fields))
  in
  Printf.printf
    "%-14s %-16s %4s %s\n"
    "oracle"
    "file"
    "n"
    (String.concat " " (List.map (Printf.sprintf "%8s") fields));
  List.iter
    (fun (name, _) ->
       List.iter
         (fun (file, runs) ->
            line
              name
              (Filename.basename file)
              (List.filter (fun (n, _, _) -> n = name) runs))
         loaded)
    oracles;
  print_newline ();
  List.iter (fun (file, runs) -> line "all" (Filename.basename file) runs) loaded
;;

let compare old new_ =
  let old = load old
  and new_ = load new_ in
  let pairs name =
    List.filter_map
      (fun (n, seed, kv) ->
         if n = name
         then
           List.find_map
             (fun (n', seed', kv') ->
                if n' = name && seed' = seed
                then Some (List.assoc "final" kv, List.assoc "final" kv')
                else None)
             new_
         else None)
      old
  in
  let line label pairs =
    let count f = List.length (List.filter f pairs) in
    let ratios = List.map (fun (a, b) -> float b /. float a) pairs in
    let sorted = List.sort compare ratios in
    let median =
      match List.length sorted with
      | 0 -> nan
      | n -> List.nth sorted (n / 2)
    in
    Printf.printf
      "%-14s %4d smaller %4d equal %4d larger   median ratio %.2f\n"
      label
      (count (fun (a, b) -> b < a))
      (count (fun (a, b) -> b = a))
      (count (fun (a, b) -> b > a))
      median
  in
  List.iter (fun (name, _) -> line name (pairs name)) oracles;
  line "all" (List.concat_map (fun (name, _) -> pairs name) oracles)
;;

let show file name seed =
  let printing = ref false in
  In_channel.with_open_text file In_channel.input_lines
  |> List.iter (fun line ->
    if
      String.starts_with ~prefix:" " line
      || String.starts_with ~prefix:"|" line
      || line = ""
    then (if !printing && String.starts_with ~prefix:"|" line then print_endline line)
    else (
      printing := String.starts_with ~prefix:[%string "%{name} %{seed} "] line;
      if !printing then print_endline line))
;;

let () =
  let usage () =
    prerr_endline
      "usage: bench run ORACLE SEED [-o FILE] | grid OUT [-seeds N] [-jobs J] | summary \
       OUT... | compare OLD NEW | show OUT ORACLE SEED | rate N | compile N";
    exit 2
  in
  let rec opt name default = function
    | k :: v :: rest -> if k = name then int_of_string v else opt name default rest
    | _ -> default
  in
  match List.tl (Array.to_list Sys.argv) with
  | [ "run"; name; seed ] -> run name (int_of_string seed) None
  | [ "run"; name; seed; "-o"; file ] -> run name (int_of_string seed) (Some file)
  | "grid" :: out :: opts ->
    grid out ~seeds:(opt "-seeds" 30 opts) ~jobs:(opt "-jobs" 6 opts)
  | "summary" :: (_ :: _ as files) -> summary files
  | [ "compare"; old; new_ ] -> compare old new_
  | [ "show"; file; name; seed ] -> show file name seed
  | [ "rate"; n ] -> rate (int_of_string n)
  | [ "compile"; n ] -> compile (int_of_string n)
  | _ -> usage ()
;;
