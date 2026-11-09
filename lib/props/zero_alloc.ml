open Config
open Ty
open Ctx
open Gen_ty
open Env

(* A [@zero_alloc] function, called between two reads of the words allocated.
   The checker decides which of these it accepts; a rejected one is dropped. *)
let test ctx env gen =
  let fn = fresh ctx "za" in
  let measure = fresh ctx "zm" in
  let params = List.init (int_in ctx 1 3) (fun _ -> fresh ctx "a", any_type ctx) in
  let result = any_type ctx in
  let strict = if flip ctx then " strict" else "" in
  let body = quietly (fun () -> gen.expr (bind_all (closure env) params) result) in
  let args =
    String.concat
      " "
      (List.map
         (fun (_, param_ty) ->
            [%string "(%{quietly (fun () -> gen.expr (pure env) param_ty)})"])
         params)
  in
  let param_decls =
    String.concat
      " "
      (List.map (fun (param, param_ty) -> [%string "(%{param} : %{param_ty#Ty})"]) params)
  in
  let param_names = String.concat " " (List.map fst params) in
  let show =
    if is_num result || not (restricted result)
    then [%string "print_endline (%{Printer.printer result} r)"]
    else "()"
  in
  (* The erased version keeps the function and its printed result, so all versions
     print the same. *)
  if !Config.erase
  then
    Markers.test
      fn
      [%string
        {|let %{fn} %{param_decls} : %{result#Ty} = %{body}
let () = let r = %{fn} %{args} in %{show}
|}]
  else
    Markers.test
      fn
      [%string
        {|let[@zero_alloc%{strict}] %{fn} %{param_decls} : %{result#Ty} = %{body}
let[@inline never] %{measure} %{param_decls} = let w0 = minor_words () in let r = (%{fn} [@inlined never]) %{param_names} in let w1 = minor_words () in #(Fu.sub w1 w0, r)
let () = let #(d, r) = %{measure} %{args} in if Fu.to_float d <> 0. then print_endline ("%{Markers.failure}%{fn} allocated " ^ show_float (Fu.to_float d) ^ " words"); %{show}
|}]
;;

(* The function a zero_alloc rejection names. *)
let rejected msg =
  Option.bind (Text.find msg "Annotation check for zero_alloc") (fun from ->
    let failed_on = " failed on function " in
    Option.map
      (fun found ->
         let start = found + String.length failed_on in
         let rec end_of_name i =
           if i < String.length msg && not (List.mem msg.[i] [ ' '; '\n' ])
           then end_of_name (i + 1)
           else i
         in
         let path =
           String.split_on_char '.' (String.sub msg start (end_of_name start - start))
         in
         List.nth path (List.length path - 1))
      (Text.find ~from msg failed_on))
;;

let drop fn = Markers.cut ~opening:"(*[" ~closing:"(*]" ~keep:(( <> ) fn)
