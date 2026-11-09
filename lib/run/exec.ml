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
  | Hung (* timed out where a backend of the same kind finished quickly *)

let spawn ~dir argv =
  let out = Filename.concat dir [%string "out%{Random.bits ()#Int}"] in
  let err = out ^ ".err" in
  let open_for_writing path = Unix.openfile path [ O_WRONLY; O_CREAT; O_TRUNC ] 0o644 in
  let out_fd = open_for_writing out
  and err_fd = open_for_writing err in
  let pid =
    Unix.create_process_env
      (List.hd argv)
      (Array.of_list argv)
      clean_env
      Unix.stdin
      out_fd
      err_fd
  in
  Unix.close out_fd;
  Unix.close err_fd;
  ( pid
  , fun () ->
      ( In_channel.with_open_bin out In_channel.input_all
      , In_channel.with_open_bin err In_channel.input_all ) )
;;

let wait_all ~timeout pids =
  let start = Unix.gettimeofday () in
  let finished = Array.make (List.length pids) None in
  let rec poll () =
    let now = Unix.gettimeofday () in
    List.iteri
      (fun i pid ->
         if Option.is_none finished.(i)
         then (
           match Unix.waitpid [ WNOHANG ] pid with
           | 0, _ when now -. start > timeout ->
             Unix.kill pid Sys.sigkill;
             ignore (Unix.waitpid [] pid);
             finished.(i) <- Some (Timeout, timeout)
           | 0, _ -> ()
           | _, WEXITED c -> finished.(i) <- Some (Exited c, now -. start)
           | _, (WSIGNALED s | WSTOPPED s) ->
             finished.(i) <- Some (Signaled s, now -. start)))
      pids;
    if Array.exists Option.is_none finished
    then (
      Unix.sleepf 0.002;
      poll ())
  in
  poll ();
  Array.to_list (Array.map Option.get finished)
;;

let show_exit = function
  | Exited c -> [%string "exit %{c#Int}"]
  | Signaled s -> [%string "signal %{s#Int}"]
  | Timeout -> "timeout"
  | Hung -> "hung while a similar backend finished quickly"
;;

type result =
  | Compile_error of string
  | Ran of exit * string * string

(* Splits a program at the boundary line into two modules. The second opens the
   first, so code is inlined across modules. File names differ per backend. *)
let modules ~index source =
  let suffix = if index = 0 then "" else [%string "_%{index#Int}"] in
  let main = [%string "prog%{suffix}.ml"] in
  let boundary = Program.module_boundary in
  match Text.find source boundary with
  | None -> [ main, source ]
  | Some i ->
    let after_boundary = i + String.length boundary in
    [ [%string "m1%{suffix}.ml"], String.sub source 0 i
    ; ( main
      , [%string "open M1%{suffix}\n"]
        ^ String.sub source after_boundary (String.length source - after_boundary) )
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
           (fun index b ->
              let dir = Filename.concat root (string_of_int index) in
              Sys.mkdir dir 0o755;
              (* The toplevel takes one script, so the program is not split into
                 modules. *)
              let files =
                if is_toplevel b
                then [ "prog.ml", source_for b source ]
                else modules ~index (source_for b source)
              in
              List.iter
                (fun (file, text) ->
                   Out_channel.with_open_bin (Filename.concat dir file) (fun oc ->
                     output_string oc text))
                files;
              dir, List.map (fun (file, _) -> Filename.concat dir file) files)
           backends
       in
       let dirs = List.map fst prepared in
       let exe dir = Filename.concat dir "prog.exe" in
       (* macOS scans each new executable on first launch, which can take up to
          2s. Bytecode avoids this by running prog.exe with ocamlrun. *)
       let run b dir =
         let compiler_path = List.hd b.argv in
         if is_toplevel b
         then b.argv @ [ "-w"; "-a"; "-nocwd"; Filename.concat dir "prog.ml" ]
         else if is_bytecode b
         then (
           let debug_runtime = List.mem "d" b.argv in
           [ Filename.concat
               (Filename.dirname compiler_path)
               (if debug_runtime then "ocamlrund" else "ocamlrun")
           ; exe dir
           ])
         else [ exe dir ]
       in
       let compiles =
         List.map2
           (fun b (dir, files) ->
              if is_toplevel b
              then spawn ~dir [ "/usr/bin/true" ]
              else
                spawn
                  ~dir
                  (b.argv
                   @ [ "-w"; "-a"; "-nocwd"; "-I"; dir ]
                   @ files
                   @ [ "-o"; exe dir ]))
           backends
           prepared
       in
       let compiled = List.map fst (wait_all ~timeout:120. (List.map fst compiles)) in
       let runs =
         List.map2
           (fun (b, dir) status ->
              match status with
              | Exited 0 -> Some (spawn ~dir (run b dir))
              | _ -> None)
           (List.combine backends dirs)
           compiled
       in
       let run_timeout = 10. in
       let ran = wait_all ~timeout:run_timeout (List.filter_map (Option.map fst) runs) in
       let ran_backends =
         List.filter_map
           (fun (b, run) -> Option.map (fun _ -> b) run)
           (List.combine backends runs)
       in
       (* Bytecode and the debug runtime are much slower, so a timeout is compared
          only with backends of the same kind. The toplevel also compiles as it
          runs, so it is compared with none. *)
       let kind b =
         if is_toplevel b then None else Some (is_bytecode b, List.mem "d" b.argv)
       in
       let finished_quickly b =
         kind b <> None
         && List.exists2
              (fun other (status, seconds) ->
                 kind other = kind b && status <> Timeout && seconds < run_timeout /. 10.)
              ran_backends
              ran
       in
       let ran =
         List.map2
           (fun b (status, _) ->
              if status = Timeout && finished_quickly b then Hung else status)
           ran_backends
           ran
       in
       let rec combine compiles compiled runs ran =
         match compiles, compiled, runs, ran with
         | [], [], [], _ -> []
         | (_, cout) :: compiles, status :: compiled, None :: runs, ran ->
           let out, err = cout () in
           Compile_error [%string "%{show_exit status}\n%{out}%{err}"]
           :: combine compiles compiled runs ran
         | _ :: compiles, _ :: compiled, Some (_, rout) :: runs, status :: ran ->
           let out, err = rout () in
           Ran (status, out, err) :: combine compiles compiled runs ran
         | _ -> assert false
       in
       (* The toplevel reports a type error or compiler crash when it runs. *)
       let compiled_late b = function
         | Ran ((Exited 2 as status), out, err)
           when is_toplevel b
                && (Text.contains err "Error:" || Text.contains err ">> Fatal error") ->
           Compile_error [%string "%{show_exit status}\n%{out}%{err}"]
         | result -> result
       in
       combine compiles compiled runs ran
       |> List.map2 compiled_late backends
       |> List.map2
            (fun dir -> function
               | Compile_error msg -> Compile_error (Text.remove_all (dir ^ "/") msg)
               | result -> result)
            dirs)
;;

let observable = function
  | Compile_error _ -> `Compile_error
  | Ran (status, out, _) -> `Ran (status, out)
;;

let report backends results =
  let body = function
    | Compile_error msg -> [%string "compile error\n%{msg}"]
    | Ran (status, out, err) -> [%string "%{show_exit status}\n%{out}%{err}"]
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
  |> List.map (fun (text, names) ->
    [%string {|--- %{String.concat ", " names}: %{text}|}])
  |> String.concat "\n"
;;
