(* Equivalence modulo inputs: an expression between (*<k*) and (*>k*) that the
   original never evaluates can be replaced with any expression of its type,
   here one generated in its place and kept in [regions], and the output must
   not change. Only the regions drawn as prunable are replaced, so dead code
   also varies. *)
let regions : (string * (string * bool)) list ref = ref []
let has_regions source = Text.contains source "(*<"
let hits_tag = "emi hits:"

(* The original, recording which regions it evaluates and printing them to
   stderr at exit, even after an uncaught exception. Its zero_alloc checks are
   dropped, since the checker may reject one before the run drops that test. *)
let covered source =
  let source = Markers.without_all [ "[@zero_alloc strict]"; "[@zero_alloc]" ] source in
  {|let emi_hits = Hashtbl.create 64
let emi_hit k = Hashtbl.replace emi_hits k ()
let () = at_exit (fun () -> prerr_string "\n|}
  ^ hits_tag
  ^ {|"; Hashtbl.iter (fun k () -> prerr_string (" " ^ k)) emi_hits; prerr_newline ())
|}
  ^ Markers.relabel
      ~opening:"(*<"
      (fun k -> [%string {|(emi_hit "%{k}"; |}])
      (Markers.relabel ~opening:"(*>" (Fun.const ")") source)
;;

let hits err =
  Option.map
    (fun i ->
       let start = i + String.length hits_tag in
       let stop =
         Option.value (String.index_from_opt err start '\n') ~default:(String.length err)
       in
       String.split_on_char ' ' (String.sub err start (stop - start)))
    (Text.find err hits_tag)
;;

(* The original with each prunable region it never evaluates replaced. *)
let pruned hits =
  Markers.cut
    ~by:(fun k -> "(" ^ fst (List.assoc k !regions) ^ ")")
    ~opening:"(*<"
    ~closing:"(*>"
    ~keep:(fun k -> List.mem k hits || not (snd (List.assoc k !regions)))
;;
