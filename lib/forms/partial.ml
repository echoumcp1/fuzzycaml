open Config
open Ty
open Ctx
open Gen_ty
open Env

let partial ctx env ty gen =
  let expr = gen.expr in
  let fn = fresh ctx "f" in
  let arity = int_in ctx 1 4 in
  let env = closure env in
  let params, body_env =
    List.fold_left
      (fun (params, body_env) i ->
         let param = fresh ctx "a" in
         let kind =
           if i = arity - 1
           then `Positional
           else
             choose
               ctx
               [ (fun () -> `Positional); (fun () -> `Labeled); (fun () -> `Optional) ]
         in
         let param_ty, decl, arg =
           match kind with
           | `Positional ->
             let param_ty, arg = gen.of_shape env (Any all_types) in
             param_ty, [%string "(%{param} : %{param_ty#Ty})"], Some (true, paren arg)
           | `Labeled ->
             let param_ty, arg = gen.of_shape env (Any value_types) in
             ( param_ty
             , [%string "~(%{param} : %{param_ty#Ty})"]
             , Some (false, [%string "~%{param}:(%{arg})"]) )
           | `Optional ->
             let param_ty, default = gen.of_shape env (Any value_types) in
             param_ty, [%string "?(%{param} : %{param_ty#Ty} = %{default})"], None
         in
         params @ [ param, param_ty, kind, decl, arg ], bind body_env param param_ty)
      ([], env)
      (List.init arity Fun.id)
  in
  let arg ~omittable (param, param_ty, kind, _, arg) =
    match kind with
    | `Positional | `Labeled -> arg
    | `Optional ->
      choose
        ctx
        ([ (fun () -> Some (false, [%string "~%{param}:(%{expr env param_ty})"]))
         ; (fun () -> Some (false, [%string "?%{param}:(Some %{expr env param_ty})"]))
         ; (fun () -> Some (false, [%string "?%{param}:None"]))
         ]
         @ if omittable then [ (fun () -> None) ] else [])
  in
  (* An optional argument can only be left out before a positional one. *)
  let rec args = function
    | [] -> []
    | param :: rest ->
      let omittable = List.exists (fun (_, _, kind, _, _) -> kind = `Positional) rest in
      let arg = arg ~omittable param in
      Option.to_list arg @ args rest
  in
  (* Labeled arguments commute; positional ones keep their order. *)
  let shuffle args =
    let moved, kept =
      List.partition (fun (pos, _) -> (not pos) && flip ~p:0.3 ctx) args
    in
    String.concat " " (List.map snd (kept @ moved))
  in
  let rec chunks = function
    | [] -> []
    | params ->
      let count = int_in ctx 1 (List.length params) in
      let first = List.filteri (fun i _ -> i < count) params in
      let rest = List.filteri (fun i _ -> i >= count) params in
      shuffle (args first) :: chunks rest
  in
  let attr = pick ctx [ ""; "[@inline never]"; "[@inline]"; "[@specialise]" ] in
  let head =
    choose
      ctx
      [ (fun () -> fn)
      ; (fun () -> [%string "(%{fn} [@inlined never])"])
      ; (fun () -> [%string "(Sys.opaque_identity %{fn})"])
      ]
  in
  let call =
    match chunks params with
    | [] -> assert false
    | first :: rest ->
      List.fold_left
        (fun applied_so_far chunk ->
           choose
             ctx
             ([ (fun () -> [%string "(%{applied_so_far} %{chunk})"])
              ; (fun () -> [%string "((Sys.opaque_identity %{applied_so_far}) %{chunk})"])
              ; (fun () ->
                  let applied = fresh ctx "q" in
                  [%string "(let %{applied} = %{applied_so_far} in %{applied} %{chunk})"])
              ]
              @
              if !Config.ox_mode
              then [ (fun () -> [%string "(%{applied_so_far} %{chunk} [@nontail])"]) ]
              else []))
        [%string "(%{head} %{first})"]
        rest
  in
  let decls = String.concat " " (List.map (fun (_, _, _, decl, _) -> decl) params) in
  [%string "(let%{attr} %{fn} %{decls} : %{ty#Ty} = %{expr body_env ty} in %{call})"]
;;

let forms ctx env ty gen =
  boost
    (if (not (restricted ty)) && on "partial"
     then [ (fun () -> partial ctx env ty gen) ]
     else [])
;;
