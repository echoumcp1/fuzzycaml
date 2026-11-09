let p = Printf.sprintf

(* In props mode, which version of the generated program a backend compiles:
   the original, the erased program checked to use no extensions and compiled
   with few optimizations, the variant with neutral wrappers, or the original
   with the regions it never evaluates replaced. *)
type version =
  | Original
  | Erased
  | Variant
  | Emi

type backend =
  { name : string
  ; argv : string list
  ; version : version
  }

let read_process cmd =
  let ic = Unix.open_process_args_in cmd.(0) cmd in
  let out = In_channel.input_all ic in
  match Unix.close_process_in ic with
  | WEXITED 0 -> Some (String.trim out)
  | _ -> None
;;

let switch_bin switch =
  read_process [| "opam"; "var"; "--switch"; switch; "bin" |]
  |> Option.map (fun bin -> switch, bin)
;;

(* NEON builtins compile to instructions, but the object file still names
   their symbols, so the linker needs empty definitions. Built once. *)
let neon_stubs =
  lazy
    (let dir = Filename.temp_dir "fuzzycaml" "neon" in
     let c = Filename.concat dir "neon_stubs.c" in
     let o = Filename.concat dir "neon_stubs.o" in
     Out_channel.with_open_bin c (fun oc ->
       List.iter (fun s -> Printf.fprintf oc "void %s(void) {}\n" s) (Neon.symbols ()));
     if Sys.command (Filename.quote_command "cc" [ "-c"; c; "-o"; o ]) <> 0
     then failwith "could not compile the NEON stubs";
     o)
;;

let discover ~ox =
  let switches =
    match read_process [| "opam"; "switch"; "list"; "-s" |] with
    | Some out -> String.split_on_char '\n' out |> List.filter (( <> ) "")
    | None -> []
  in
  let switches =
    match Sys.getenv_opt "FUZZYCAML_SWITCHES" with
    | None -> switches
    | Some only ->
      List.filter (fun s -> List.mem s switches) (String.split_on_char ',' only)
  in
  List.filter_map switch_bin switches
  |> List.concat_map (fun (switch, bin) ->
    let ocamlopt = Filename.concat bin "ocamlopt" in
    let ocamlc = Filename.concat bin "ocamlc" in
    if not (Sys.file_exists ocamlopt)
    then []
    else (
      let config var = read_process [| ocamlopt; "-config-var"; var |] in
      let flambda2 = config "flambda2" = Some "true" in
      let flambda = config "flambda" = Some "true" || flambda2 in
      let neon = ox && flambda2 && config "architecture" = Some "arm64" in
      if neon then Config.neon := true;
      let libs ext =
        if ox
        then
          (if neon then [ "-extension"; "simd_beta" ] else [])
          @ [ "-extension"
            ; "comprehensions"
            ; "-I"
            ; "+stdlib_stable"
            ; "-I"
            ; "+stdlib_upstream_compatible"
            ; "stdlib_stable" ^ ext
            ; "stdlib_upstream_compatible" ^ ext
            ]
        else []
      in
      let nat flags =
        (ocamlopt
         :: "-dcmm-invariants"
         :: (if flambda then [ "-dflambda-invariants" ] else []))
        @ libs ".cmxa"
        @ (if neon then [ Lazy.force neon_stubs ] else [])
        @ flags
      in
      let opt suffix flags =
        { name = [%string "%{switch}/ocamlopt%{suffix}"]
        ; argv = nat flags
        ; version = Original
        }
      in
      let byte =
        { name = [%string "%{switch}/ocamlc"]
        ; argv = (ocamlc :: libs ".cma") @ [ "-runtime-variant"; "d" ]
        ; version = Original
        }
      in
      let toplevel =
        { name = [%string "%{switch}/ocaml"]
        ; argv = Filename.concat bin "ocaml" :: libs ".cma"
        ; version = Original
        }
      in
      if ox
      then
        if not flambda2
        then []
        else
          [ byte
          ; opt "-Oclassic" [ "-Oclassic" ]
          ; opt "" []
          ; opt "-O3" [ "-O3" ]
          ; opt "-toggles" []
          ; toplevel
          ]
      else if flambda2
      then []
      else
        [ byte; opt "" []; opt "-linscan" [ "-linscan" ]; toplevel ]
        @
        if flambda
        then
          [ opt "-O3" [ "-O3" ]
          ; opt "-Oclassic" [ "-Oclassic" ]
          ; opt "-O3-linscan" [ "-O3"; "-linscan" ]
          ; opt
              "-O3-aggressive"
              [ "-O3"
              ; "-unbox-closures"
              ; "-inline"
              ; "1000"
              ; "-rounds"
              ; "4"
              ; "-inline-max-depth"
              ; "3"
              ; "-remove-unused-arguments"
              ; "-unsafe"
              ; "-runtime-variant"
              ; "d"
              ]
          ]
        else
          (* Programs do not rely on bounds checks. *)
          [ opt "-unsafe-inline" [ "-unsafe"; "-inline"; "1000"; "-runtime-variant"; "d" ]
          ; opt "-compact" [ "-compact"; "-no-float-const-prop"; "-no-insn-sched" ]
          ; opt "-inline-g" [ "-inline"; "200"; "-g" ]
          ]))
;;

let extra () =
  match Sys.getenv_opt "FUZZYCAML_EXTRA" with
  | None -> []
  | Some spec ->
    String.split_on_char ';' spec
    |> List.filter (( <> ) "")
    |> List.map (fun entry ->
      match String.index_opt entry '=' with
      | None -> failwith ("FUZZYCAML_EXTRA: expected name=command, got " ^ entry)
      | Some i ->
        { name = String.sub entry 0 i
        ; argv =
            String.sub entry (i + 1) (String.length entry - i - 1)
            |> String.split_on_char ' '
            |> List.filter (( <> ) "")
        ; version = Original
        })
;;

let effect_syntax ~ox backends =
  (not ox)
  && List.for_all
       (fun b ->
          match read_process [| List.hd b.argv; "-vnum" |] with
          | Some v ->
            (match String.split_on_char '.' (String.trim v) with
             | major :: minor :: _ -> (int_of_string major, int_of_string minor) >= (5, 3)
             | _ -> false)
          | None -> false)
       backends
;;

let is_toplevel b = Filename.basename (List.hd b.argv) = "ocaml"

(* Library features newer compilers add, each with a program that uses it. *)
let probes =
  [ ( "atomic_loc"
    , "type r = { mutable a : int [@atomic] }\n\
       let f r = Atomic.Loc.fetch_and_add [%atomic.loc r.a] 1" )
  ; "atomic_array", "let f () = Atomic.Array.fetch_and_add (Atomic.Array.make 4 0) 1 2"
  ; "popcount", "let f x = Int.popcount x + Int.leading_zeros x + Int.trailing_zeros x"
  ]
;;

(* The probes that the ocamlc next to every backend's compiler accepts. *)
let probe backends =
  let dir = Filename.temp_dir "fuzzycaml" "probe" in
  let file = Filename.concat dir "probe.ml" in
  let bins =
    List.sort_uniq
      compare
      (List.map (fun b -> Filename.dirname (List.hd b.argv)) backends)
  in
  let compiles source bin =
    Out_channel.with_open_bin file (fun oc -> output_string oc source);
    Sys.command
      (Filename.quote_command
         ~stdout:"/dev/null"
         ~stderr:"/dev/null"
         (Filename.concat bin "ocamlc")
         [ "-c"; "-w"; "-a"; "-o"; Filename.concat dir "probe.cmo"; file ])
    = 0
  in
  let found =
    List.filter_map
      (fun (name, source) ->
         if List.for_all (compiles source) bins then Some name else None)
      probes
  in
  ignore (Sys.command (Filename.quote_command "rm" [ "-rf"; dir ]));
  found
;;
