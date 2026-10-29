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
   - OxCaml -use-ssa: the validator rejects the SSA pipeline's CFG.
   - OxCaml arm64: fmov with a float32# constant it cannot encode,
     (1 + m/16) * 2^k for k in 61..68.
   - OxCaml -flambda2-match-in-match at -O3: a match alias left free in the
     unit.
   - Flambda: a float array built in a GADT branch that is dead for the
     element type. *)
let known_compile_crash msg =
  List.exists
    (contains msg)
    [ "Selection.size_expr"
    ; "Matching: impossible empty matrix in a Total match"
    ; "Matching.comp_exit"
    ; "While verifying locations destroyed at raise"
    ; "CFG comparison MISMATCH"
    ; "not expected to be free in whole-compilation-unit term"
    ; "Bad definition for float array member"
    ]
  || (contains msg "expected compatible register or floating-point constant"
      && contains msg "fmov")
;;

let known_bug backends results source =
  let reference = observable (List.hd results) in
  let agrees r = observable r = reference in
  let odd =
    List.filter_map
      (fun (b, r) -> if agrees r then None else Some b)
      (List.combine backends results)
  in
  let odd_names = List.map (fun b -> b.name) odd in
  (* Whether the odd backends, changed by [f], agree with the reference on
     [source]. *)
  let odd_agree f source = List.for_all agrees (run_all (List.map f odd) source) in
  odd <> []
  && (List.for_all
        (fun r ->
           agrees r
           ||
           match r with
           | Compile_error msg -> known_compile_crash msg
           (* -flambda2-reaper with phantom lets aborts at run time. *)
           | Ran (_, _, err) -> contains err "Dead variable in bound pattern")
        results
      ||
      (* After a nested perform, native code leaves a shallow fiber's effect
         handler pointing into the minor heap, and the GC later crashes. Matches
         only if every crashing backend, rebuilt with the debug runtime, fails
         the runtime's check for it. *)
      (List.for_all
         (fun r ->
            agrees r
            ||
            match r with
            | Ran (Signaled s, _, _) -> List.mem s Sys.[ sigbus; sigsegv; sigabrt; sigtrap ]
            | _ -> false)
         results
       && List.for_all
            (function
              | Ran (_, _, err) -> contains err "Assertion failed: !Is_young(v)"
              | Compile_error _ -> false)
            (run_all
               (List.map (fun b -> { b with argv = b.argv @ [ "-runtime-variant"; "d" ] }) odd)
               source))
      ||
      (* Trunk -linscan ignores the interference that keeps the results of
         native Atomic exchange, compare-and-set and fetch-and-add out of their
         arguments' registers. Matches only if the odd backends agree once those
         are ordinary calls. *)
      (contains source "Atomic."
       && List.for_all
            (fun n -> contains n "trunk" && String.ends_with ~suffix:"-linscan" n)
            odd_names
       && odd_agree Fun.id (atomic_shim ^ source))
      ||
      (* Flambda's -Oclassic reads a constant field of a lifted block as the
         block itself. Matches only if the odd backends agree when compiled by
         FUZZYCAML_FIXED_OCLASSIC, an ocamlopt with the fix. *)
      match Sys.getenv_opt "FUZZYCAML_FIXED_OCLASSIC" with
      | None -> false
      | Some fixed ->
        List.for_all
          (fun n -> contains n "flambda/" && String.ends_with ~suffix:"-Oclassic" n)
          odd_names
        && odd_agree (fun b -> { b with argv = fixed :: List.tl b.argv }) source)
;;
