open Config
open Ty
open Ctx
open Env

let rec_value ctx env ty expr =
  let fn = fresh ctx "f" in
  let count = fresh ctx "n" in
  let body env = expr (bind (closure env) count Int) ty in
  (* The count's parity picks the result, so it reaches the output. *)
  [ (fun () ->
      let lazy_var = fresh ctx "lz" in
      [%string
        "(let rec %{lazy_var} : %{ty#Ty} Lazy.t = lazy %{expr (lazy_body env) ty} and \
         %{fn} : int -> %{ty#Ty} = fun %{count} -> if %{count} <= 0 then Lazy.force \
         %{lazy_var} else if %{count} = 1 then %{body env} else %{fn} (%{count} - 2) in \
         %{fn} (%{expr env Int} land 7))"])
  ; (fun () ->
      let value = fresh ctx "v" in
      let pair = fresh ctx "pr" in
      [%string
        "(let %{value} : %{ty#Ty} = %{expr env ty} in let rec %{pair} = (%{fn}, \
         %{value}) and %{fn} : int -> %{ty#Ty} = fun %{count} -> if %{count} <= 0 then \
         snd %{pair} else if %{count} = 1 then %{body env} else (fst %{pair}) (%{count} \
         - 2) in (fst %{pair}) (%{expr env Int} land 7))"])
  ; (fun () ->
      let other = fresh ctx "g" in
      [%string
        "(let rec %{fn} (%{count} : int) : %{ty#Ty} = if %{count} <= 0 then %{body env} \
         else %{other} (%{count} - 1) and %{other} (%{count} : int) : %{ty#Ty} = if \
         %{count} <= 0 then %{body env} else %{fn} (%{count} - 1) in %{fn} (%{expr env \
         Int} land 15))"])
  ]
  @
  match ty with
  | List elem_ty ->
    [ (fun () ->
        let first = fresh ctx "a" in
        let second = fresh ctx "b" in
        let cycle = fresh ctx "c" in
        [%string
          "(let %{first} : %{elem_ty#Ty} = %{expr env elem_ty} in let %{second} : \
           %{elem_ty#Ty} = %{expr env elem_ty} in let rec %{cycle} = %{first} :: \
           %{second} :: %{cycle} in take (%{expr env Int} land 15) %{cycle})"])
    ]
  | _ -> []
;;

let forms ctx env ty gen =
  boost
    (if (not (restricted ty)) && on "recvals" then rec_value ctx env ty gen.expr else [])
;;
