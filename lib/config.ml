
(* Whether OxCaml features are generated. *)
let ox_mode = ref false
let use_effect_syntax = ref false

(* (child, parent): polymorphic variant t<child> extends t<parent>. *)
let poly_parent : (int * int) list ref = ref []

(* (boxed, unboxed): an unboxed record type with a boxed record's fields. *)
let twins : (int * int) list ref = ref []

(* Swarm testing: each program enables a random subset of features, and
   shrinking can disable the ones a failure does not need. *)
let all_features =
  [ "arrays"; "atomics"; "deep"; "effect_syntax"; "effects"; "exits"; "exns"; "gadt"; "gc"; "lazy"
  ; "locals"; "loops"; "manyargs"; "modules"; "opaque"; "partial"; "poly"; "records"
  ; "recvals"; "samebranch"; "shallow"; "strings"; "tmc"
    (* OxCaml only *)
  ; "mutables"; "numbers"; "or_null"; "urecords"; "utuples"
  ]

let features = ref all_features
let on feature = List.mem feature !features

(* Repeats an enabled feature's choices so it is generated more often. *)
let boost l = List.concat (List.init 5 (fun _ -> l))

(* Declared types that contain unboxed or uncomparable values (rejected by
   polymorphic comparison), and the unboxed records. *)
let mixed : bool array ref = ref [||]
let urec : bool array ref = ref [||]
