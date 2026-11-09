open Hegel

type draw =
  | Int_draw of int
  | Float_draw of float

(* In props mode, the draws of the program being generated, so it can be
   generated again with the same choices. *)
let recorded = ref []
let to_replay = ref None
let replaying () = Option.is_some !to_replay

let next_replayed () =
  match !to_replay with
  | Some (value :: rest) ->
    to_replay := Some rest;
    Some value
  | Some [] -> failwith "Draw: replay ran out of draws"
  | None -> None
;;

let replayable_int draw =
  match next_replayed () with
  | Some (Int_draw value) -> value
  | Some (Float_draw _) -> failwith "Draw: replayed a float as an int"
  | None ->
    let value = draw () in
    if !Config.props then recorded := Int_draw value :: !recorded;
    value
;;

let int tc lo hi =
  replayable_int (fun () -> draw_silent tc (integers ~min_value:lo ~max_value:hi ()))
;;

let bool ?p tc =
  replayable_int (fun () -> Bool.to_int (draw_silent tc (booleans ?p ()))) = 1
;;

let unbounded tc = replayable_int (fun () -> draw_silent tc (integers ()))

let float tc generator =
  match next_replayed () with
  | Some (Float_draw value) -> value
  | Some (Int_draw _) -> failwith "Draw: replayed an int as a float"
  | None ->
    let value = draw_silent tc generator in
    if !Config.props then recorded := Float_draw value :: !recorded;
    value
;;

let replay f =
  to_replay := Some (List.rev !recorded);
  Fun.protect ~finally:(fun () -> to_replay := None) f
;;
