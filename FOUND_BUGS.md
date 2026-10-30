# Found bugs

Compiler bugs found by fuzzycaml that had not been reported before.

## OCaml

- [ocaml/ocaml#15196](https://github.com/ocaml/ocaml/issues/15196): native code leaves a dangling minor-heap pointer in a shallow fiber's effect handler after a nested `perform`, and the GC later crashes.
- [ocaml/ocaml#15202](https://github.com/ocaml/ocaml/issues/15202) (fixed): flambda `-Oclassic` reads a constant field of a block as the block itself, so a `char` read from it is garbage.

## OxCaml

- [oxcaml/oxcaml#7737](https://github.com/oxcaml/oxcaml/issues/7737): `-flambda2-reaper` calls a Cmm handler declared with 0 arguments with 1, which `-dcmm-invariants` rejects.
- [oxcaml/oxcaml#7746](https://github.com/oxcaml/oxcaml/issues/7746): on arm64, a `float32#` constant such as 2^62 is emitted as an `fmov` immediate it cannot encode, and the assembler rejects it.
- [oxcaml/oxcaml#7763](https://github.com/oxcaml/oxcaml/issues/7763): `-flambda2-match-in-match` crashes with `Variable unboxed_field_0 not expected to be free in whole-compilation-unit term`, depending on the file name.
- [oxcaml/oxcaml#7789](https://github.com/oxcaml/oxcaml/issues/7789): `ocamlopt` crashes with `Invalid_argument("fold_left_map2")` on a local function applied to the contents of a `ref`.
