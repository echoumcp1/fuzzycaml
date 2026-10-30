let p = Printf.sprintf

type backend =
  { name : string
  ; argv : string list
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
      let libs ext =
        if ox
        then
          [ "-I"
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
        @ flags
      in
      let opt suffix flags =
        { name = [%string "%{switch}/ocamlopt%{suffix}"]; argv = nat flags }
      in
      let byte =
        { name = [%string "%{switch}/ocamlc"]
        ; argv = (ocamlc :: libs ".cma") @ [ "-runtime-variant"; "d" ]
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
          ]
      else if flambda2
      then []
      else
        [ byte; opt "" []; opt "-linscan" [ "-linscan" ] ]
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
          (* programs do not rely on bounds checks *)
          [ opt "-unsafe-inline" [ "-unsafe"; "-inline"; "1000"; "-runtime-variant"; "d" ]
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
        })
;;

let effect_syntax ~ox backends =
  (not ox)
  && List.for_all
       (fun b ->
          match read_process [| List.hd b.argv; "-version" |] with
          | Some v ->
            (match String.split_on_char '.' (String.trim v) with
             | major :: minor :: _ -> (int_of_string major, int_of_string minor) >= (5, 3)
             | _ -> false)
          | None -> false)
       backends
;;
