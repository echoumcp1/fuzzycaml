let occurs_at s i sub =
  let n = String.length sub in
  let rec go j = j = n || (s.[i + j] = sub.[j] && go (j + 1)) in
  i + n <= String.length s && go 0
;;

let find ?(from = 0) s sub =
  let rec go i =
    if i + String.length sub > String.length s
    then None
    else if occurs_at s i sub
    then Some i
    else go (i + 1)
  in
  go from
;;

let contains s sub = find s sub <> None

let replace_all sub ~by s =
  let b = Buffer.create (String.length s) in
  let i = ref 0 in
  while !i < String.length s do
    if occurs_at s !i sub
    then (
      Buffer.add_string b by;
      i := !i + String.length sub)
    else (
      Buffer.add_char b s.[!i];
      incr i)
  done;
  Buffer.contents b
;;

let remove_all sub s = replace_all sub ~by:"" s

let is_alphanumeric = function
  | '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' -> true
  | _ -> false
;;

(* Whether [s] contains [word] with no letter or digit on either side. *)
let mentions s word =
  let n = String.length word in
  let rec go from =
    match find ~from s word with
    | None -> false
    | Some i ->
      ((i = 0 || not (is_alphanumeric s.[i - 1]))
       && (i + n = String.length s || not (is_alphanumeric s.[i + n])))
      || go (i + 1)
  in
  go 0
;;
