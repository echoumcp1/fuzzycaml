open Backend
open Exec

(* Known bugs, recognised by which backends disagree with the reference (the
   first backend), so that a run continues past them. *)
let atomic_shim =
  {|module Atomic = struct
  include Atomic
  let[@inline never] exchange a v = let old = get a in set a v; old
  let[@inline never] compare_and_set a o n = if get a == o then (set a n; true) else false
  let[@inline never] fetch_and_add a n = let old = get a in set a (old + n); old
  let[@inline never] incr a = set a (get a + 1)
  let[@inline never] decr a = set a (get a - 1)
end
|}
;;

(* Compile crashes:
   - ocamlopt without flambda: an allocation field that is a mutable let,
     such as an unused ref.
   - Releases before trunk: a redundant or-pattern with a guard after a
     catch-all (Matching.comp_exit in 5.2 and OxCaml).
   - OxCaml -Oclassic: a dead trap handler around a call that cannot raise,
     where linscan reads a ref from an unset register.
   - OxCaml -Oclassic: a raise inside a try (Array.iter2 in Cfg_selectgen),
     and a float# read in an unreachable match arm.
   - OxCaml -flambda2-expert-inline-effects-in-cmm.
   - OxCaml -use-ssa: the validator rejects the SSA pipeline's CFG.
   - OxCaml arm64: fmov with a float32# constant it cannot encode,
     (1 + m/16) * 2^k for k in 61..68.
   - OxCaml -flambda2-match-in-match at -O3: a match alias left free in the
     unit. *)
let known_compile_crash msg =
  contains msg "Selection.size_expr"
  || contains msg "Matching: impossible empty matrix in a Total match"
  || contains msg "Matching.comp_exit"
  || contains msg "While verifying locations destroyed at raise"
  || contains msg "Array.iter2: arrays must have the same length"
  || contains msg "Duplicate order for bindings when flushing"
  || contains msg "Illegal move between registers of differing types"
  || contains msg "CFG comparison MISMATCH"
  || contains msg "not expected to be free in whole-compilation-unit term"
  || (contains msg "expected compatible register or floating-point constant" && contains msg "fmov");;

let known_bug backends results source =
  let obs = List.map observable results in
  let reference = List.hd obs in
  let odd =
    List.filter_map
      (fun (b, o) -> if o = reference then None else Some b.name)
      (List.combine backends obs)
  in
  let compile_crash =
    odd <> []
    && List.for_all
         (fun r ->
            observable r = reference
            ||
            match r with
            | Compile_error msg -> known_compile_crash msg
            (* -flambda2-reaper with phantom lets aborts at run time. *)
            | Ran (_, _, err) -> contains err "Dead variable in bound pattern")
         results
  in
  compile_crash
  ||
  (* After a nested perform, native code leaves a shallow fiber's effect handler
     pointing into the minor heap, and the GC later crashes. Matches only if
     every crashing backend, rebuilt with the debug runtime, fails the runtime's
     check for it. *)
  (odd <> []
   && List.for_all
        (fun (b, r) ->
           (not (List.mem b.name odd))
           ||
           match r with
           | Ran (Signaled s, _, _) -> List.mem s Sys.[ sigbus; sigsegv; sigabrt; sigtrap ]
           | _ -> false)
        (List.combine backends results)
   && List.for_all
        (function
          | Ran (_, _, err) -> contains err "Assertion failed: !Is_young(v)"
          | Compile_error _ -> false)
        (run_all
           (List.filter_map
              (fun b ->
                 if List.mem b.name odd
                 then Some { b with argv = b.argv @ [ "-runtime-variant"; "d" ] }
                 else None)
              backends)
           source))
  ||
  (* Trunk -linscan ignores the interference that keeps the results of native
     Atomic exchange, compare-and-set and fetch-and-add out of their arguments'
     registers. Matches only if the odd backends agree once those are ordinary
     calls. *)
  (odd <> []
   && contains source "Atomic."
   && List.for_all
        (fun n -> contains n "trunk" && String.ends_with ~suffix:"-linscan" n)
        odd
   &&
   let odd_backends = List.filter (fun b -> List.mem b.name odd) backends in
   List.for_all
     (fun r -> observable r = reference)
     (run_all odd_backends (atomic_shim ^ source)))
  ||
  (* Flambda's -Oclassic reads a constant field of a lifted block as the block
     itself. Matches only if the odd backends agree when compiled by
     FUZZYCAML_FIXED_OCLASSIC, an ocamlopt with the fix. *)
  match Sys.getenv_opt "FUZZYCAML_FIXED_OCLASSIC" with
  | None -> false
  | Some fixed ->
    odd <> []
    && List.for_all (fun n -> contains n "flambda/" && String.ends_with ~suffix:"-Oclassic" n) odd
    &&
    let odd_backends =
      List.filter_map
        (fun b -> if List.mem b.name odd then Some { b with argv = fixed :: List.tl b.argv } else None)
        backends
    in
    List.for_all (fun r -> observable r = reference) (run_all odd_backends source)
;;
