open Ty
open Ctx
open Env

let tmc ctx env elem_ty expr =
  let fn = fresh ctx "go" in
  let count = fresh ctx "n" in
  let head = fresh ctx "x" in
  let body_env = bind (closure env) count Int in
  let call = [%string "%{fn} (%{count} - 1)"] in
  let cons () =
    [%string
      "(let %{head} : %{elem_ty#Ty} = %{expr body_env elem_ty} in %{head} :: %{call})"]
  in
  let step =
    choose
      ctx
      [ cons
      ; (fun () -> [%string "(if %{expr body_env Bool} then %{cons ()} else %{call})"])
      ; (fun () ->
          let head = fresh ctx "h" in
          [%string
            "(match %{expr body_env (List elem_ty)} with [] -> %{call} | %{head} :: _ -> \
             %{head} :: %{call})"])
      ; (fun () ->
          let second = fresh ctx "y" in
          [%string
            "(let %{head} : %{elem_ty#Ty} = %{expr body_env elem_ty} in let %{second} : \
             %{elem_ty#Ty} = %{expr body_env elem_ty} in %{head} :: %{second} :: \
             %{call})"])
      ]
  in
  [%string
    "(let[@tail_mod_cons] rec %{fn} (%{count} : int) : %{(List elem_ty)#Ty} = if \
     %{count} <= 0 then %{expr body_env (List elem_ty)} else %{step} in (%{fn}[@tailcall \
     false]) (%{expr env Int} land 15))"]
;;
