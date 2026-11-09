open Backend

(* Flags that must not change a program's meaning, mostly off by default. The
   toggles backend draws a few per program. *)
let ox_toggles =
  [ "-cfg-merge-blocks"
  ; "-reorder-blocks-random 7"
  ; "-vectorize"
  ; "-g"
  ; "-g -gdwarf-may-alter-codegen"
  ; "-dcfg-invariants"
  ; "-debug-long-frames-threshold 0"
  ; "-function-layout source"
  ; "-no-cfg-prologue-shrink-wrap"
  ; "-cfg-prologue-shrink-wrap-threshold 1"
  ; "-no-cfg-value-propagation"
  ; "-no-cfg-peephole-optimize"
  ; "-no-cfg-eliminate-dead-trap-handlers"
  ; "-cfg-stack-checks-threshold 0"
  ; "-caml-apply-inline-fast-path"
  ; "-flambda2-advanced-meet"
  ; "-no-flambda2-join-points"
  ; "-no-flambda2-unbox-along-intra-function-control-flow"
  ; "-flambda2-expert-max-unboxing-depth 0"
  ; "-flambda2-expert-cmm-safe-subst"
  ; "-flambda2-expert-phantom-lets"
  ; "-flambda2-backend-cse-at-toplevel"
  ; "-flambda2-inline-max-depth 0"
  ; "-flambda2-inline-threshold 1000 -flambda2-inline-max-depth 6"
  ; "-flambda2-cse-depth 0"
  ; "-flambda2-join-depth 0"
  ; "-regalloc irc"
  ; "-regalloc ls"
  ; "-regalloc gi"
  ; "-regalloc-linscan-threshold 0"
  ; "-runtime-variant d"
  ; "-flambda2-reaper"
  ; "-use-ssa"
  ; "-flambda2-result-types-all-functions"
  ; "-flambda2-expert-can-inline-recursive-functions"
  ; "-flambda2-match-in-match"
  ; "-flambda2-join-algorithm n-way"
  ; "-experimental-optimizations"
  ; "-cfg-block-layout"
  ; "-cfg-copy-propagation"
  ; "-use-ssa -no-ssa-validate"
  ; "-use-ssa -no-ssa-simplify"
  ; "-dbranch-relaxation-max-displacement 16"
  ; "-dbranch-relaxation-max-displacement 1024"
  ; "-verify-binary-emitter"
  ; "-flambda2-expert-cont-specialization-threshold 1000"
  ; "-no-flambda2-simplify-stubs"
  ; "-g -gdwarf-may-alter-codegen -gdwarf-may-alter-codegen-experimental"
  ]
;;

(* Each compiler only gets the flags its -help lists, since newer versions add
   flags. *)
let help = Hashtbl.create 4

let supports compiler toggle =
  let text =
    match Hashtbl.find_opt help compiler with
    | Some help_text -> help_text
    | None ->
      let help_text = Option.value ~default:"" (read_process [| compiler; "-help" |]) in
      Hashtbl.add help compiler help_text;
      help_text
  in
  Text.contains text ("  " ^ List.hd (String.split_on_char ' ' toggle) ^ " ")
;;

let with_toggles tc backends =
  let levels = [ "-O3"; ""; "-O2"; "-Oclassic"; "-O4" ] in
  let level = List.nth levels (Draw.int tc 0 (List.length levels - 1)) in
  let picked = List.filter (fun _ -> Draw.bool ~p:0.08 tc) ox_toggles in
  List.map
    (fun b ->
       if String.ends_with ~suffix:"-toggles" b.name
       then (
         let picked = List.filter (supports (List.hd b.argv)) picked in
         let flags =
           List.concat_map (String.split_on_char ' ') (level :: picked)
           |> List.filter (( <> ) "")
         in
         let reaper = List.mem "-flambda2-reaper" flags || List.mem "-O4" flags in
         (* The reaper with phantom lets leaves dangling symbols, so they are
            never combined; experimental DWARF codegen turns phantom lets on.
            The reaper (also on at -O4) makes -dcmm-invariants and
            -dcfg-invariants reject correct programs, so both checks are
            dropped with it. *)
         let drop banned l =
           if reaper then List.filter (fun f -> not (List.mem f banned)) l else l
         in
         let flags =
           drop
             [ "-flambda2-expert-phantom-lets"
             ; "-gdwarf-may-alter-codegen-experimental"
             ; "-dcfg-invariants"
             ]
             flags
         in
         let argv = drop [ "-dcmm-invariants" ] b.argv in
         { b with
           name = [%string {|%{b.name} %{String.concat " " flags}|}]
         ; argv = argv @ flags
         })
       else b)
    backends
;;
