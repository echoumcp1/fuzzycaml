open Backend

let clean_env =
  Unix.environment ()
  |> Array.to_list
  |> List.filter (fun kv ->
    not
      (List.exists
         (fun prefix -> String.starts_with ~prefix kv)
         [ "OCAML"; "CAML_LD_LIBRARY_PATH"; "OPAM_SWITCH_PREFIX" ]))
  |> Array.of_list
;;

type exit =
  | Exited of int
  | Signaled of int
  | Timeout

(* Runs [argv] in [dir], returning its exit and its stdout and stderr. *)
let spawn ~dir argv =
  let out = Filename.concat dir (p "out%d" (Random.bits ())) in
  let err = out ^ ".err" in
  let fd path = Unix.openfile path [ O_WRONLY; O_CREAT; O_TRUNC ] 0o644 in
  let fo = fd out
  and fe = fd err in
  let pid =
    Unix.create_process_env (List.hd argv) (Array.of_list argv) clean_env Unix.stdin fo fe
  in
  Unix.close fo;
  Unix.close fe;
  ( pid
  , fun () ->
      ( In_channel.with_open_bin out In_channel.input_all
      , In_channel.with_open_bin err In_channel.input_all ) )
;;

let wait_all ~timeout pids =
  let deadline = Unix.gettimeofday () +. timeout in
  let rec wait pid =
    match Unix.waitpid [ WNOHANG ] pid with
    | 0, _ when Unix.gettimeofday () > deadline ->
      Unix.kill pid Sys.sigkill;
      ignore (Unix.waitpid [] pid);
      Timeout
    | 0, _ ->
      Unix.sleepf 0.002;
      wait pid
    | _, WEXITED c -> Exited c
    | _, (WSIGNALED s | WSTOPPED s) -> Signaled s
  in
  List.map wait pids
;;

let show_exit = function
  | Exited c -> p "exit %d" c
  | Signaled s -> p "signal %d" s
  | Timeout -> "timeout"
;;

let strip ~prefix s =
  let n = String.length prefix in
  let b = Buffer.create (String.length s) in
  let i = ref 0 in
  while !i < String.length s do
    if !i + n <= String.length s && String.sub s !i n = prefix
    then i := !i + n
    else (
      Buffer.add_char b s.[!i];
      incr i)
  done;
  Buffer.contents b
;;

type result =
  | Compile_error of string
  | Ran of exit * string * string

let find s sub =
  let n = String.length sub in
  let rec go i =
    if i + n > String.length s then None else if String.sub s i n = sub then Some i else go (i + 1)
  in
  go 0
;;

let contains s sub = find s sub <> None

(* Splits a program at the boundary line into two modules. The second opens the
   first, so code is inlined across modules. *)
let modules source =
  let boundary = Program.module_boundary in
  match find source boundary with
  | None -> [ "prog.ml", source ]
  | Some i ->
    let j = i + String.length boundary in
    [ "m1.ml", String.sub source 0 i
    ; "prog.ml", "open M1\n" ^ String.sub source j (String.length source - j)
    ]
;;

let run_all ?(source_for = Fun.const Fun.id) backends source =
  let root = Filename.temp_dir "fuzzycaml" "" in
  Fun.protect
    ~finally:(fun () ->
      ignore (Sys.command (Filename.quote_command "rm" [ "-rf"; root ])))
    (fun () ->
       let prepared =
         List.mapi
           (fun i b ->
              let dir = Filename.concat root (string_of_int i) in
              Sys.mkdir dir 0o755;
              let files = modules (source_for b source) in
              List.iter
                (fun (f, text) ->
                   Out_channel.with_open_bin (Filename.concat dir f) (fun oc ->
                     output_string oc text))
                files;
              dir, List.map (fun (f, _) -> Filename.concat dir f) files)
           backends
       in
       let dirs = List.map fst prepared in
       let exe dir = Filename.concat dir "prog.exe" in
       (* macOS scans each new executable on first launch, which can take up to
          2s. Bytecode avoids this by running prog.exe with ocamlrun. *)
       let run b dir =
         let c = List.hd b.argv in
         if String.starts_with ~prefix:"ocamlc" (Filename.basename c)
         then (
           let d = List.mem "d" b.argv in
           [ Filename.concat (Filename.dirname c) (if d then "ocamlrund" else "ocamlrun"); exe dir ])
         else [ exe dir ]
       in
       let compiles =
         List.map2
           (fun b (dir, files) ->
              spawn ~dir (b.argv @ [ "-w"; "-a"; "-I"; dir ] @ files @ [ "-o"; exe dir ]))
           backends
           prepared
       in
       let compiled = wait_all ~timeout:120. (List.map fst compiles) in
       let runs =
         List.map2
           (fun (b, dir) status ->
              match status with
              | Exited 0 -> Some (spawn ~dir (run b dir))
              | _ -> None)
           (List.combine backends dirs)
           compiled
       in
       let ran = wait_all ~timeout:10. (List.filter_map (Option.map fst) runs) in
       let rec combine compiles compiled runs ran =
         match compiles, compiled, runs, ran with
         | [], [], [], _ -> []
         | (_, cout) :: compiles, status :: compiled, None :: runs, ran ->
           let o, e = cout () in
           Compile_error (p "%s\n%s%s" (show_exit status) o e)
           :: combine compiles compiled runs ran
         | _ :: compiles, _ :: compiled, Some (_, rout) :: runs, status :: ran ->
           let o, e = rout () in
           Ran (status, o, e) :: combine compiles compiled runs ran
         | _ -> assert false
       in
       combine compiles compiled runs ran
       |> List.map2
            (fun dir -> function
               | Compile_error msg -> Compile_error (strip ~prefix:(dir ^ "/") msg)
               | r -> r)
            dirs)
;;

let observable = function
  | Compile_error _ -> `Compile_error
  | Ran (status, out, _) -> `Ran (status, out)
;;

(* Backends with identical results are listed together. *)
let report backends results =
  let body = function
    | Compile_error msg -> p "compile error\n%s" msg
    | Ran (status, out, err) -> p "%s\n%s%s" (show_exit status) out err
  in
  List.fold_left2
    (fun groups b r ->
       let text = body r in
       if List.mem_assoc text groups
       then
         List.map
           (fun (t, names) -> t, if t = text then names @ [ b.name ] else names)
           groups
       else groups @ [ text, [ b.name ] ])
    []
    backends
    results
  |> List.map (fun (text, names) -> p "--- %s: %s" (String.concat ", " names) text)
  |> String.concat "\n"
;;
