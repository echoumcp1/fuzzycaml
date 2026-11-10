(* Known bugs, recognized by which backends disagree with the reference (the
   first backend that compiled), so that a run continues past them. *)
open Backend
open Exec

(* Compile crashes:
   - Releases before trunk: a redundant or-pattern with a guard after a
     catch-all (Matching.comp_exit in 5.2 and OxCaml).
   - OxCaml -Oclassic: a dead trap handler around a call that cannot raise,
     where linscan reads a ref from an unset register.
   - OxCaml -flambda2-match-in-match at -O3: a match alias left free in the
     unit.
   - Flambda: a float array built in a GADT branch that is dead for the
     element type.
   - OxCaml: an apply_cont with fewer arguments than its continuation, from
     a local function applied to the contents of a ref.
   Bugs that the patched switches fix are not listed. *)
let known_compile_crash msg =
  List.find_opt
    (Text.contains msg)
    [ "Matching.comp_exit"
    ; "While verifying locations destroyed at raise"
    ; "not expected to be free in whole-compilation-unit term"
    ; "Bad definition for float array member"
    ; "fold_left_map2"
    ; "do not match arguments of"
    ; "arguments but got apply_cont"
    ; "Bytegen.merge_repr"
    ; "No size found for Static binding"
    ]
;;

(* The SSA validator reports a mismatch on correct code when caml_apply takes the
   inline fast path. *)
let known_backend_crash b msg =
  match known_compile_crash msg with
  | Some _ as found -> found
  | None ->
    if
      List.mem "-caml-apply-inline-fast-path" b.argv
      && Text.contains msg "CFG comparison MISMATCH"
    then Some "SSA validator with the caml_apply fast path"
    else None
;;

(* Bytecode: a memprof callback that grows a fiber's stack during the
   allocation in [perform] leaves the continuation on the freed stack.
   [Effect.Shallow.fiber] performs one itself. Matches only if every crashing
   backend is bytecode and agrees with the others once memprof is off. *)
let memprof_perform ~rerun backends results source =
  let crashed, others =
    List.partition
      (fun (_, r) ->
         match r with
         | Ran (Signaled _, _, _) -> true
         | _ -> false)
      (List.combine backends results)
  in
  let without_memprof source =
    String.split_on_char '\n' source
    |> List.filter (fun l ->
      not (String.starts_with ~prefix:"let () = try ignore (Gc.Memprof" l))
    |> String.concat "\n"
  in
  match others with
  | (_, expected) :: _
    when Text.contains source "Gc.Memprof.start"
         && crashed <> []
         && List.for_all (fun (b, _) -> is_bytecode b) crashed
         && List.for_all
              (fun r -> observable r = observable expected)
              (rerun ~edit:without_memprof (List.map fst crashed)) ->
    Some "memprof callback in perform (bytecode)"
  | _ -> None
;;

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

(* Trunk -linscan ignores the interference that keeps the results of native
   Atomic exchange, compare-and-set and fetch-and-add out of their arguments'
   registers, so on trunk switches, which are named after their commit,
   [atomic_shim] replaces them with ordinary functions. Released versions call
   C for these. *)
let on_trunk name =
  let switch = List.hd (String.split_on_char '/' name) in
  match String.split_on_char '-' switch with
  | [ "fz"; "ocaml"; sha ] | [ "fz"; "ocaml"; sha; "flambda" ] ->
    String.length sha = 10
    && String.for_all
         (function
           | '0' .. '9' | 'a' .. 'f' -> true
           | _ -> false)
         sha
  | _ -> false
;;

let known_bug ~rerun backends results source =
  let reference =
    observable
      (Option.value
         (List.find_opt
            (function
              | Ran _ -> true
              | Compile_error _ -> false)
            results)
         ~default:(List.hd results))
  in
  let agrees result = observable result = reference in
  let odd =
    List.filter_map
      (fun (b, result) -> if agrees result then None else Some b)
      (List.combine backends results)
  in
  let odd_names = List.map (fun b -> b.name) odd in
  let odd_agree edit_backend =
    List.for_all agrees (rerun ~edit:Fun.id (List.map edit_backend odd))
  in
  let first_of checks = List.find_map (fun check -> check ()) checks in
  if odd = []
  then None
  else
    first_of
      [ (fun () ->
          let reasons =
            List.filter_map
              (fun (b, result) ->
                 if agrees result
                 then None
                 else
                   Some
                     (match result with
                      (* The reaper can drop the code of a partially applied
                         function that is still referenced. *)
                      | Compile_error msg
                        when List.mem "-flambda2-reaper" b.argv || List.mem "-O4" b.argv
                        ->
                        (match known_backend_crash b msg with
                         | Some _ as found -> found
                         | None ->
                           if
                             Text.contains msg "Undefined symbols"
                             || Text.contains msg "undefined reference"
                           then Some "reaper: undefined symbol"
                           else None)
                      | Compile_error msg -> known_backend_crash b msg
                      (* -flambda2-reaper with phantom lets aborts at run time. *)
                      | Ran (_, _, err) ->
                        if Text.contains err "Dead variable in bound pattern"
                        then Some "reaper: dead variable"
                        else None))
              (List.combine backends results)
          in
          if List.for_all Option.is_some reasons then List.hd reasons else None)
        (* After a nested perform, native code leaves a shallow fiber's effect
           handler pointing into the minor heap, and the GC later crashes.
           Matches only if every crashing backend, rebuilt with the debug
           runtime, fails the runtime's check for it. *)
      ; (fun () ->
          if
            List.for_all
              (fun result ->
                 agrees result
                 ||
                 match result with
                 | Ran (Signaled signal, _, _) ->
                   List.mem signal Sys.[ sigbus; sigsegv; sigabrt; sigtrap ]
                 | _ -> false)
              results
            && List.for_all
                 (function
                   | Ran (_, _, err) -> Text.contains err "Assertion failed: !Is_young(v)"
                   | Compile_error _ -> false)
                 (rerun
                    ~edit:Fun.id
                    (List.map
                       (fun b -> { b with argv = b.argv @ [ "-runtime-variant"; "d" ] })
                       odd))
          then Some "effect handler pointing into the minor heap"
          else None)
        (* A list comprehension to max_int, or downto min_int, does not stop.
           Matches only if the program has such a range and all backends agree
           once comprehension ranges move one step inward. *)
      ; (fun () ->
          let at_max = "= (max_int - 15) + ("
          and at_min = "= min_int + (" in
          let inward source =
            source
            |> Text.replace_all at_max ~by:"= (max_int - 16) + ("
            |> Text.replace_all at_min ~by:"= (min_int + 1) + ("
          in
          let hung = function
            | Ran (Hung, _, _) -> true
            | _ -> false
          in
          if
            (Text.contains source at_max || Text.contains source at_min)
            && List.exists hung results
            &&
            match rerun ~edit:inward backends with
            | first :: rest ->
              (not (hung first))
              && List.for_all (fun r -> observable r = observable first) rest
            | [] -> false
          then Some "list comprehension to max_int"
          else None)
        (* Flambda's -Oclassic reads a constant field of a lifted block as the
           block itself. Matches only if the odd backends agree when compiled
           by FUZZYCAML_FIXED_OCLASSIC, an ocamlopt with the fix. *)
      ; (fun () ->
          match Sys.getenv_opt "FUZZYCAML_FIXED_OCLASSIC" with
          | None -> None
          | Some fixed ->
            if
              List.for_all
                (fun name ->
                   Text.contains name "flambda/"
                   && String.ends_with ~suffix:"-Oclassic" name)
                odd_names
              && odd_agree (fun b -> { b with argv = fixed :: List.tl b.argv })
            then Some "flambda -Oclassic constant field"
            else None)
      ]
;;
