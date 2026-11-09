(* In props mode, generated code marks the parts that only some versions of the
   program keep with comments that each version's text is cut from:
   - a neutral wrapper's own code is between (*{k*) and (*}k*),
   - a zero_alloc test is between (*[k*) and (*]k*),
   - an EMI region is between (*<k*) and (*>k*). *)

let wrapper k code = [%string "(*{%{k}*)%{code}(*}%{k}*)"]
let test k code = [%string "(*[%{k}*)%{code}(*]%{k}*)"]
let region k code = [%string "(*<%{k}*)%{code}(*>%{k}*)"]

(* A line that a program prints when one of its checks fails. *)
let failure = "!! "

let read_key s ~opening from =
  let start = from + String.length opening in
  let stop = Option.get (Text.find ~from:start s "*)") in
  String.sub s start (stop - start), stop + 2
;;

(* Replaces each part from [opening ^ k ^ "*)"] to the next [closing ^ k ^ "*)"]
   with [by k], for the [k] that [keep] rejects. *)
let cut ?(by = Fun.const "") ~opening ~closing ~keep s =
  let rec go s from =
    match Text.find ~from s opening with
    | None -> s
    | Some i ->
      let k, after_marker = read_key s ~opening i in
      if keep k
      then go s after_marker
      else (
        let close = closing ^ k ^ "*)" in
        let j = Option.get (Text.find ~from:after_marker s close) + String.length close in
        let replacement = by k in
        go
          (String.sub s 0 i ^ replacement ^ String.sub s j (String.length s - j))
          (i + String.length replacement))
  in
  go s 0
;;

(* Replaces each marker [opening ^ k ^ "*)"] with [by k]. *)
let relabel ~opening by s =
  let rec go s from =
    match Text.find ~from s opening with
    | None -> s
    | Some i ->
      let k, after_marker = read_key s ~opening i in
      let replacement = by k in
      go
        (String.sub s 0 i
         ^ replacement
         ^ String.sub s after_marker (String.length s - after_marker))
        (i + String.length replacement)
  in
  go s 0
;;

let without_wrappers = cut ~opening:"(*{" ~closing:"(*}" ~keep:(Fun.const false)
let has_wrappers source = Text.contains source "(*{"

(* The source without markers, for reports. *)
let clean s =
  List.fold_left
    (fun s opening -> relabel ~opening (Fun.const "") s)
    s
    [ "(*{"; "(*}"; "(*["; "(*]"; "(*<"; "(*>" ]
;;

let without_all words s = List.fold_left (fun s word -> Text.remove_all word s) s words
