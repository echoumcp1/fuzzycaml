open Hegel
open Backend
open Check

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let sample = List.mem "--sample" args in
  let ox = List.mem "--ox" args in
  let test_cases =
    match List.filter (fun a -> a <> "--sample" && a <> "--ox") args with
    | [ n ] -> int_of_string n
    | _ -> if sample then 5 else 200
  in
  let settings =
    { (Settings.create ~test_cases ()) with
      suppress_health_check = [ Too_slow; Test_cases_too_large; Large_initial_test_case ]
    ; database =
        (match Sys.getenv_opt "FUZZYCAML_DATABASE" with
         | Some dir -> Path dir
         | None -> Disabled)
    }
  in
  if sample
  then
    run_hegel_test ~settings (fun tc ->
      print_endline (Program.program ~ox ~effect_syntax:(not ox) tc);
      print_endline "(* ---- *)")
  else (
    let backends = discover ~ox @ extra () in
    List.iter
      (fun b -> Printf.printf "backend %s: %s\n%!" b.name (String.concat " " b.argv))
      backends;
    if List.length backends < 2 then failwith "need at least two backends";
    at_exit (fun () ->
      Printf.printf
        "ran %d programs, %d timed out, %d hit known bugs\n%!"
        !cases
        !timeouts
        !known);
    let effect_syntax = effect_syntax ~ox backends in
    Printf.printf "effect syntax: %b\n%!" effect_syntax;
    let run ?failure_blobs () =
      run_hegel_test
        ~settings
        ~database_key:"fuzzycaml"
        ?failure_blobs
        (check ~ox ~effect_syntax backends)
    in
    Lift.run ~generate:(fun tc -> ignore (generate ~ox ~effect_syntax backends tc)) run)
;;
