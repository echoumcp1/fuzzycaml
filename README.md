# WARNING

This fuzzer is an experiment in autonomous software development by large language models and external shrinking passes. I used Claude Opus 5.5 on medium effort and instrumented Hegel locally to provide information on generation time, shrink time, shrink passes, and shrink failures, among other metrics. Claude used this data to improve generation. I also periodically checked the programs Claude produced and suggested fixes or improvements, but almost all of the code in this repository is not human checked. 

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
- `--props`: check one OxCaml compiler against itself: wrappers that keep a program's meaning, `[@zero_alloc]` functions that must not allocate, the program with OxCaml syntax and optimization hints erased (built with `-Oclassic`), and the program with code it never runs replaced must all print the same output.

Environment variables:
- `FUZZYCAML_SWITCHES=a,b`: use only these opam switches, in this order; the first is the reference.
- `FUZZYCAML_EXTRA="name=compiler flags;..."`: add backends.
- `FUZZYCAML_DATABASE=dir`: save failures in Hegel's database at `dir`, so a later run replays them first.
- `FUZZYCAML_REPLAY=blob`: replay a failure blob (printed after a failure as `rerun with`) and report it as is, without shrinking; fails if it no longer reproduces.
- `FUZZYCAML_FEATURES=a,b`: enable these features in every program (see `all_features` in `lib/generator/config.ml`).
- `FUZZYCAML_SAVE=dir`: write programs that hit a known bug to `dir/known<pid>-<n>.ml`, and rejected ones to `dir/rejected<pid>-<n>.ml`.
- `FUZZYCAML_FIXED_OCLASSIC=<ocamlopt>`: a compiler with the flambda `-Oclassic` constant field fix (see `lib/run/known.ml`).

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
known/         programs that hit known bugs or were rejected
fuzz.exe       the binary the workers run
stop           create this file to stop the run
```

`watch.sh` exits when a log contains a failure and prints its name. It stops the run if more than 40 logs appear (workers failing at startup) or if less than 10GB of disk is free.

# Layout

```
bin/fuzzycaml.ml      command line
lib/text.ml           string search
lib/run/              backend discovery and flags, compiling and running, known bugs, checking
lib/types/            types, literals, patterns, printers, drawing types
lib/generator/        generation state, prelude, expressions and whole programs
lib/forms/            one module per generator feature
lib/props/            versions of a program for --props: wrappers, EMI, zero_alloc tests
run.sh, watch.sh      long runs
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

The generator prefers variables that are not used yet, so that function parameters are not dead. Every choice is a Hegel draw and every expression is a span, so shrinking can remove features, flags and subexpressions and still produce a well-typed program.

An expression's span consists of the choices for its type and for the actual expression. They are forced where the
context fixes the type (e.g. the operands of `+`) and drawn where it does not (e.g. a `let`-bound expression). Whether
an expression is a leaf is a choice to allow the shrinker to trim expression trees. Different choices can give the same
program, so the fuzzer compiles each program once and caches the result.

# Backends
Each opam switch adds these backends:
- Without `--ox` (OxCaml switches are skipped): `ocamlc`, `ocamlopt`, `ocamlopt -linscan`. Non-flambda switches add `ocamlopt -unsafe -inline 1000`, `-compact -no-float-const-prop -no-insn-sched` and `-inline 200 -g`. Flambda switches add `-O3`, `-Oclassic`, `-O3 -linscan`, and an aggressive `-O3`.
- With `--ox` (flambda2 switches only): `ocamlc`, `ocamlopt` at `-Oclassic`, the default level and `-O3`, and a toggles backend that draws an optimization level and a set of flags for each program.
- Both add the toplevel, `ocaml`, which runs the program as a script.

`ocamlc` and one native backend per switch use the debug runtime. `ocamlopt` runs with `-dcmm-invariants`, and flambda backends also with `-dflambda-invariants`. The first backend that compiles is the reference. A release `ocamlc` can be added as a second reference with `FUZZYCAML_EXTRA`; a mismatch against it alone may be a bug fixed in trunk.

Backends compile in parallel in separate temporary directories with `-w -a` and a cleaned environment. Compilation times out after 120 s and execution after 10 s. Programs that time out are discarded.

# Results
For each program, in order:
1. No backend compiled it: failure if any output has `Fatal error` or an assembler or linker error; otherwise a generator bug, which is saved and skipped.
2. A run timed out: discarded.
3. It matches a known bug: discarded and counted.
4. A backend was killed by a signal or raised an uncaught exception other than `Exit`: failure.
5. Backends differ in compile result, exit status, or output: failure.

During shrinking, only the reference and the first disagreeing backend are run. The report shows the shrunk program, the backends grouped by result, and a `failure_blobs` line that reproduces it. At the end, the fuzzer prints how many programs it ran and compiled, timed out, matched known bugs, and were rejected.
