open Config
open Ty
open Ctx
open Gen_ty
open Env

type kind =
  | Positional
  | Labeled
  | Optional

type argument =
  { positional : bool
  ; text : string
  }

(* A parameter, with its declaration and, unless it is optional, the argument
   drawn with it. *)
type param =
  { name : string
  ; ty : ty
  ; kind : kind
  ; decl : string
  ; fixed_arg : argument option
  }

(* A function applied to its arguments in several steps. *)
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
           then Positional
           else
             choose
               ctx
               [ (fun () -> Positional); (fun () -> Labeled); (fun () -> Optional) ]
         in
         let param_ty, decl, fixed_arg =
           match kind with
           | Positional ->
             let param_ty, arg = gen.of_shape env (Any all_types) in
             ( param_ty
             , [%string "(%{param} : %{param_ty#Ty})"]
             , Some { positional = true; text = paren arg } )
           | Labeled ->
             let param_ty, arg = gen.of_shape env (Any value_types) in
             ( param_ty
             , [%string "~(%{param} : %{param_ty#Ty})"]
             , Some { positional = false; text = [%string "~%{param}:(%{arg})"] } )
           | Optional ->
             let param_ty, default = gen.of_shape env (Any value_types) in
             param_ty, [%string "?(%{param} : %{param_ty#Ty} = %{default})"], None
         in
         ( params @ [ { name = param; ty = param_ty; kind; decl; fixed_arg } ]
         , bind body_env param param_ty ))
      ([], env)
      (List.init arity Fun.id)
  in
  let arg ~omittable param =
    let labeled text = Some { positional = false; text } in
    match param.kind with
    | Positional | Labeled -> param.fixed_arg
    | Optional ->
      choose
        ctx
        ([ (fun () -> labeled [%string "~%{param.name}:(%{expr env param.ty})"])
         ; (fun () -> labeled [%string "?%{param.name}:(Some %{expr env param.ty})"])
         ; (fun () -> labeled [%string "?%{param.name}:None"])
         ]
         @ if omittable then [ (fun () -> None) ] else [])
  in
  (* An optional argument can only be left out before a positional one. *)
  let rec args = function
    | [] -> []
    | param :: rest ->
      let omittable = List.exists (fun param -> param.kind = Positional) rest in
      let arg = arg ~omittable param in
      Option.to_list arg @ args rest
  in
  (* Labeled arguments commute; positional ones keep their order. *)
  let shuffle args =
    let moved, kept =
      List.partition (fun arg -> (not arg.positional) && flip ~p:0.3 ctx) args
    in
    String.concat " " (List.map (fun arg -> arg.text) (kept @ moved))
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
  let decls = String.concat " " (List.map (fun param -> param.decl) params) in
  [%string "(let%{attr} %{fn} %{decls} : %{ty#Ty} = %{expr body_env ty} in %{call})"]
;;

let forms ctx env ty gen =
  boost
    (if (not (restricted ty)) && on "partial"
     then [ (fun () -> partial ctx env ty gen) ]
     else [])
;;
