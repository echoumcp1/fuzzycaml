(* After Hegel's shrinking, tries lifting an expression out of a top-level
   binding of another type, which Hegel cannot do since spans are labelled by
   type. A lift that fails the same way is shrunk again by Hegel. *)

let kind = function
  | Failure m -> List.hd (String.split_on_char '\n' m)
  | e -> Printexc.to_string e
;;

(* Regenerates a candidate tolerantly, so that draws the new context makes
   differently do not stop the replay. *)
let normalize generate c =
  let out = ref None in
  let settings =
    { (Hegel.Settings.create ~test_cases:1 ()) with
      suppress_health_check =
        Hegel.Settings.[ Too_slow; Test_cases_too_large; Large_initial_test_case ]
    ; database = Disabled
    }
  in
  (try
     Hegel.run_hegel_test ~settings (fun tc ->
       Trace.reset ();
       Trace.tolerant := Some c;
       Fun.protect ~finally:(fun () -> Trace.tolerant := None) (fun () -> generate tc);
       out := Some (List.rev !Trace.choices))
   with
   | _ -> ());
  !out
;;

(* Each candidate compiles the program again, so a large one can take long. *)
let seconds = 120.

let run ~generate (test : ?failure_blobs:string list -> unit -> unit) =
  let deadline = ref infinity in
  let rec lift best exn rounds =
    let rec go = function
      | _ when Unix.gettimeofday () > !deadline -> exn
      | [] -> exn
      | c :: rest ->
        (match test ~failure_blobs:[ Trace.blob c ] () with
         | () -> go rest
         | exception e ->
           (match !Trace.last with
            | Some s when kind e = kind exn && s.size < best.Trace.size ->
              Printf.printf "lift: %d -> %d characters\n%!" best.size s.size;
              lift s e (rounds + 1)
            | _ -> go rest))
    in
    if rounds >= 10
    then exn
    else
      go
        (List.sort_uniq compare (List.filter_map (normalize generate) (Trace.lifts best)))
  in
  match test () with
  | () -> ()
  | exception e ->
    (match !Trace.last with
     | None -> raise e
     | Some first ->
       deadline := Unix.gettimeofday () +. seconds;
       let e' = lift first e 0 in
       (match !Trace.last with
        | Some s when s != first ->
          (* replay the best, so the last report printed is its *)
          (try test ~failure_blobs:[ Trace.blob (Array.to_list s.cs) ] () with
           | _ -> ())
        | _ -> ());
       raise e')
;;
