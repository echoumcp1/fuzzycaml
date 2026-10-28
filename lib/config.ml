
(* Whether OxCaml features are generated. *)
let ox_mode = ref false
let use_effect_syntax = ref false

(* (child, parent): polymorphic variant t<child> extends t<parent>. *)
let poly_parent : (int * int) list ref = ref []

(* (boxed, unboxed): an unboxed record type with a boxed record's fields. *)
let twins : (int * int) list ref = ref []

(* Swarm testing: each program uses only some features, so the ones it does
   use are not crowded out, and a shrunk failure names the ones it needs. *)
let all_features =
  [ "atomics"; "deep"; "effect_syntax"; "effects"; "exits"; "exns"; "gadt"; "gc"; "lazy"
  ; "locals"; "loops"; "manyargs"; "modules"; "opaque"; "partial"; "poly"; "records"
  ; "recvals"; "samebranch"; "shallow"; "strings"; "tmc"
    (* OxCaml only *)
  ; "arrays"; "mutables"; "numbers"; "or_null"; "urecords"; "utuples"
  ]

let features = ref all_features
let on feature = List.mem feature !features

(* A switched-on feature's productions are one choice among many; repeating
   them makes the feature show up in the programs that switch it on. *)
let boost l = List.concat (List.init 5 (fun _ -> l))

(* The declared types that hold an unboxed or uncomparable value, which
   polymorphic comparison rejects, and the unboxed records. *)
let mixed : bool array ref = ref [||]
let urec : bool array ref = ref [||]
