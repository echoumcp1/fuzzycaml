(* Whether the program being generated may use OxCaml extensions. *)
let ox_mode = ref false

(* Whether the program may use OCaml 5.3's effect handler syntax. *)
let effect_syntax_on = ref false

(* Whether programs check properties of one compiler instead of comparing
   several. *)
let props = ref false

(* Whether generated code may contain wrappers, EMI regions, observed values and
   hashed conditions. They are left out of junk, to keep programs small, and of
   the body of a [@zero_alloc] function, which they would make allocate. *)
let checks_on = ref true

let without_checks f =
  let old = !checks_on in
  checks_on := false;
  Fun.protect ~finally:(fun () -> checks_on := old) f
;;

(* Whether programs are printed without OxCaml's modes, layouts and other
   extensions, which only change how values are represented. *)
let erase = ref false
let ox_syntax ox ocaml = if !erase then ocaml else ox

(* Pairs (i, j) where polymorphic variant type [i] extends type [j]. *)
let extended_variants : (int * int) list ref = ref []

(* Pairs (i, j) where unboxed record type [j] has the fields of record type [i]. *)
let unboxed_twins : (int * int) list ref = ref []

(* Swarm testing: each program enables a random subset of features, and
   shrinking can disable the ones a failure does not need. *)
let all_features =
  [ "arrays"
  ; "atomics"
  ; "deep"
  ; "effargs"
  ; "effect_syntax"
  ; "effects"
  ; "exits"
  ; "escapes"
  ; "exns"
  ; "gadt"
  ; "gc"
  ; "lazy"
  ; "locals"
  ; "loops"
  ; "manyargs"
  ; "modules"
  ; "opaque"
  ; "partial"
  ; "poly"
  ; "records"
  ; "recvals"
  ; "samebranch"
  ; "shallow"
  ; "strings"
  ; "tmc"
  ; "mutables"
  ; "numbers"
  ; "or_null"
  ; "urecords"
  ; "utuples"
  ; "objects"
  ; "functors"
  ; "observe"
  ; "interrupts"
  ; "bigarrays"
  ; "comprehensions"
  ; "simd"
  ]
;;

let features = ref all_features
let on feature = List.mem feature !features

(* Library features that every backend's compiler has, found by [Backend.probe]. *)
let available : string list ref = ref []
let has feature = List.mem feature !available

(* Whether the OxCaml backends target arm64, whose vector builtins [Neon] declares. *)
let neon = ref false

(* Variant constructors declared with an inline record. *)
let inline_records : string list ref = ref []

(* Repeats an enabled feature's choices so it is generated more often. *)
let boost forms = List.concat (List.init 5 (fun _ -> forms))

(* For each declared type, whether it holds a value that is not first-order. *)
let not_first_order_decls : bool array ref = ref [||]

(* For each declared type, whether it is an unboxed record. *)
let unboxed_record_decls : bool array ref = ref [||]
