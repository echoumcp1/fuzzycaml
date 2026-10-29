# About
fuzzycaml generates random OCaml programs, compiles and runs them with several compilers and flag sets, and reports compilation failures, crashes, and output mismatches. Failing programs are shrunk with Hegel before they are reported.

# How to use
You need the `hegel` opam package and the libhegel shared library (set `HEGEL_LIBHEGEL_PATH` if it is not found).

```
dune build
dune exec bin/fuzzycaml.exe -- [--sample] [--ox] [TEST_CASES]
```

- `TEST_CASES`: number of programs to try (default 200, or 5 with `--sample`).
- `--sample`: print the generated programs instead of testing them, separated by `(* ---- *)`.
- `--ox`: generate OxCaml-only features and test only OxCaml (flambda2) switches.

Environment variables:
- `FUZZYCAML_SWITCHES=a,b`: use only these opam switches.
- `FUZZYCAML_EXTRA="name=compiler flags;..."`: add backends.
- `FUZZYCAML_DATABASE=dir`: save failures in Hegel's database at `dir`, so a later run replays them first.
- `FUZZYCAML_FEATURES=a,b`: enable these features in every program (see `all_features` in `lib/config.ml`).
- `FUZZYCAML_SAVE=dir`: write programs that hit a known bug to `dir/known<pid>-<n>.ml`.
- `FUZZYCAML_FIXED_OCLASSIC=<ocamlopt>`: a compiler with the flambda `-Oclassic` constant field fix (see Known bugs).

## Long runs

```
FUZZYCAML_SWITCHES=ocaml-trunkfix,ocaml-trunkfix-flambda \
FUZZYCAML_EXTRA="ocaml-5.5.1/ocamlc=$(opam var --switch ocaml-5.5.1 bin)/ocamlc -runtime-variant d" \
  ./run.sh <dir> <hours> <workers> [fuzzer args]
./watch.sh <dir>
```

`run.sh` copies the built binary to `<dir>/fuzz.exe` and starts `<workers>` fuzzers. Each fuzzer stops at its first failure and is restarted. The run ends after `<hours>` or when `<dir>/stop` exists. When time is up, fuzzers that are shrinking a failure are left to finish; `stop` ends them too. To update the fuzzers during a run, `mv` a new binary over `<dir>/fuzz.exe`; workers pick it up when they restart.

Output in `<dir>`:
```
w<w>-<i>.log   log of worker w's i-th fuzzer; a failure ends with the shrunk program
db/w<w>-<i>/   its Hegel database, which keeps the failure even if the log is cut short
known/         programs that hit known bugs
fuzz.exe       the binary the workers run
stop           create this file to stop the run
```

`watch.sh` exits when a log contains a failure and prints its name. It stops the run if more than 40 logs appear (workers failing at startup) or if less than 10GB of disk is free.

# Layout

```
bin/fuzzycaml.ml   command line
lib/backend.ml     backend discovery
lib/exec.ml        compiling and running programs on every backend
lib/toggles.ml     the toggles backend's flags
lib/known.ml       known bug filters
lib/check.ml       checking one program
lib/config.ml      global state: OxCaml mode, enabled features, properties of declared types
lib/ty.ml          types, number conversions, type predicates
lib/printer.ml     value printers and type declarations
lib/prelude.ml     helper definitions at the start of every program
lib/ctx.ml         generation context and drawing helpers
lib/gen_ty.ml      random types
lib/literal.ml     literals
lib/pattern.ml     declared types and patterns
lib/env.ml         variables in scope
lib/effects.ml     effect handlers
lib/gadt.ml        GADT terms
lib/ox.ml          OxCaml-only expressions
lib/stress.ml      expressions aimed at the backend (spills, many arguments, GC, string loads)
lib/forms.ml       other expression forms (partial application, atomics, exceptions, lazy, recursive values, TMC)
lib/specific.ml    operations on each type
lib/generic.ml     forms at any type (let, if, match, functions, loops, try)
lib/expr.ml        expression generator
lib/program.ml     whole programs
run.sh, watch.sh   long runs
```

# Generated programs
Programs are well typed, terminate, and have deterministic output:
- Subexpressions with effects are let-bound, since evaluation order is unspecified.
- NaNs print as `nan`, and `compare` results go through `sgn`.
- Division, `mod` and `String.sub` go through total helpers in the prelude. Loop bounds and recursion counters are masked.
- The only exception raised on purpose is `Exit`, and only inside a handler for it.

A program has a prelude, up to four type declarations, optional effect declarations and atomics, and one to six top-level bindings. Each binding is printed:

```ocaml
let v3 : (int * string) list = <expression>
let () = print_endline (<printer for (int * string) list> v3)
```

Types are `int`, `bool`, `float`, `char`, `int64`, `string`, lists, options, pairs, functions, arrays, and declared records and variants (including polymorphic variants). With `--ox` there are also `float32`, small and unboxed integers, `float#` and other unboxed numbers, unboxed tuples and records, and `or_null`.

Each program enables a random subset of features, listed on its first line as `(* features: ... *)`. Disabled features are never generated, and enabled ones are weighted up. With the `modules` feature, the program is split at `(* module boundary *)` into `m1.ml` and `prog.ml` and compiled without `-opaque`, so code is inlined across modules.

The generator prefers variables that are not used yet, so that function parameters are not dead. Every choice is a Hegel draw and every expression is a labelled span, so shrinking can remove features, flags and subexpressions and still produce a well-typed program.

# Backends
Each opam switch adds these backends:
- Without `--ox` (OxCaml switches are skipped): `ocamlc`, `ocamlopt`, `ocamlopt -linscan`. Non-flambda switches add `ocamlopt -unsafe -inline 1000`. Flambda switches add `-O3`, `-Oclassic`, `-O3 -linscan`, and an aggressive `-O3`.
- With `--ox` (flambda2 switches only): `ocamlc`, `ocamlopt` at `-Oclassic`, the default level and `-O3`, and a toggles backend that draws an optimisation level and a set of flags for each program.

`ocamlc` and one native backend per switch use the debug runtime. `ocamlopt` runs with `-dcmm-invariants`, and flambda backends also with `-dflambda-invariants`. The first backend is the reference. A release `ocamlc` can be added as a second reference with `FUZZYCAML_EXTRA`; a mismatch against it alone may be a bug fixed in trunk.

Backends compile in parallel in separate temporary directories with `-w -a` and a cleaned environment. Compilation times out after 120 s and execution after 10 s. Programs that time out are discarded.

# Results
For each program, in order:
1. No backend compiled it: failure (compiler crash if any output has `Fatal error`, generator bug otherwise).
2. A run timed out: discarded.
3. It matches a known bug: discarded and counted.
4. A backend was killed by a signal or raised an uncaught exception other than `Exit`: failure.
5. Backends differ in compile result, exit status, or output: failure.

During shrinking, only the reference and the first disagreeing backend are run. The report shows the shrunk program, the backends grouped by result, and a `failure_blobs` line that reproduces it. At the end, the fuzzer prints how many programs it ran, timed out, and matched known bugs.

## Known bugs
`known_bug` recognises these by behaviour, using the backends that disagree with the reference:
- Non-flambda `ocamlopt`: `Selection.size_expr` crash.
- Releases before trunk: `Matching: impossible empty matrix in a Total match` (or `Matching.comp_exit` in 5.2 and OxCaml) on a redundant or-pattern with a guard after a catch-all.
- OxCaml `-use-ssa`: `CFG comparison MISMATCH`. This hides all `-use-ssa` validator failures.
- OxCaml `-flambda2-reaper`: `Dead variable in bound pattern` at run time.
- OxCaml reaper and invariant checks: `-dcmm-invariants` and `-dcfg-invariants` reject correct programs. The toggles backend drops both checks when the reaper is on.
- OxCaml reaper with `-g -flambda2-expert-phantom-lets`: undefined symbols at link time. The toggles backend never combines them.
- OxCaml reaper: undefined symbols at link time.
- OxCaml: `apply_cont` arity crashes (`fold_left_map2`).
- OxCaml `-dcmm-invariants` with unboxed products: programs containing `#(` or `#{` are compiled without the check.
- OxCaml arm64: `float32#` constants (1 + m/16) × 2^k with k from 61 to 68 are emitted as invalid `fmov` immediates.
- OxCaml `-flambda2-match-in-match`: `Variable ... not expected to be free in whole-compilation-unit term`.
- Flambda: `Bad definition for float array member`.
- OxCaml `-Oclassic`: `While verifying locations destroyed at raise` for a `try` whose body cannot raise.
- Native effects: a shallow handler left pointing into the minor heap after a nested `perform`. Matches when every odd backend crashes and fails `Assertion failed: !Is_young(v)` with the debug runtime.
- Trunk `-linscan` and `Atomic`: matches when the odd backends are trunk `-linscan` and agree with the reference after `Atomic` is replaced by ordinary functions. `-linscan` backends always get this replacement.
- Flambda `-Oclassic` reading a constant field of a lifted block as the block's address. Matches when the odd backends agree with the reference when compiled by `FUZZYCAML_FIXED_OCLASSIC`; without that variable the bug stops the run.
