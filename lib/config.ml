let ox_mode = ref false
let use_effect_syntax = ref false
let poly_parent : (int * int) list ref = ref []
let twins : (int * int) list ref = ref []

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
  ]
;;

let features = ref all_features
let on feature = List.mem feature !features

(* Repeats an enabled feature's choices so it is generated more often. *)
let boost l = List.concat (List.init 5 (fun _ -> l))
let mixed : bool array ref = ref [||]
let urec : bool array ref = ref [||]
