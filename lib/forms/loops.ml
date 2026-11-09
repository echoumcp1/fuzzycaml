open Config
open Ty
open Ctx
open Env

let forms ctx env ty gen =
  let expr = gen.expr in
  if (not (first_order ty)) || not (on "loops")
  then []
  else
    [ (fun () ->
        let ref_var = fresh ctx "r" in
        let loop_var = fresh ctx "i" in
        let body = expr (bind (bind env [%string "!%{ref_var}"] ty) loop_var Int) ty in
        let start = range_start ctx ~usual:"0" ~width:7 in
        [%string
          "(let %{ref_var} = ref (%{expr env ty} : %{ty#Ty}) in for %{loop_var} = \
           %{start} to %{start} + (%{expr env Int} land 7) do %{ref_var} := %{body} \
           done; !%{ref_var})"])
    ; (fun () ->
        let ref_var = fresh ctx "r" in
        let counter = fresh ctx "k" in
        let limit = fresh ctx "lim" in
        let loop_env = bind env [%string "!%{ref_var}"] ty in
        let step = expr (bind loop_env [%string "!%{counter}"] Int) ty in
        [%string
          "(let %{ref_var} = ref (%{expr env ty} : %{ty#Ty}) in let %{counter} = ref 0 \
           in let %{limit} = %{expr env Int} land 7 in while !%{counter} < %{limit} && \
           %{expr loop_env Bool} do %{ref_var} := %{step}; incr %{counter} done; \
           !%{ref_var})"])
    ; (fun () ->
        let array = fresh ctx "a" in
        let loop_var = fresh ctx "i" in
        let get = [%string "%{array}.(%{loop_var} mod Array.length %{array})"] in
        [%string
          "(let %{array} = Array.make (1 + (%{expr env Int} land 7)) %{expr env ty} in \
           for %{loop_var} = 0 to (%{expr env Int} land 7) do %{array}.((%{expr (bind \
           env loop_var Int) Int} land max_int) mod Array.length %{array}) <- %{expr \
           (bind (bind env get ty) loop_var Int) ty} done; Array.fold_left (fun (_ : \
           %{ty#Ty}) (x : %{ty#Ty}) -> x) %{array}.(0) %{array})"])
    ]
;;
