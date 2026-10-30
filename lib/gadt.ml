open Ty
open Ctx
open Env

let rec gadt ctx env ty e depth =
  let sub t = gadt ctx env t e (depth - 1) in
  let lit () = [%string "(GLit %{e env ty})"] in
  if depth <= 0
  then lit ()
  else
    choose
      ctx
      ([ lit
       ; (fun () -> [%string "(GIf (%{sub Bool}, %{sub ty}, %{sub ty}))"])
       ; (fun () -> [%string "(GFst %{sub (Pair (ty, fo_env_ty ctx env))})"])
       ; (fun () -> [%string "(GSnd %{sub (Pair (fo_env_ty ctx env, ty))})"])
       ]
       @
       match ty with
       | Int ->
         [ (fun () -> [%string "(GInt %{e env Int})"])
         ; (fun () -> [%string "(GAdd (%{sub Int}, %{sub Int}))"])
         ]
       | Bool ->
         [ (fun () -> [%string "(GBool %{e env Bool})"])
         ; (fun () -> [%string "(GLe (%{sub Int}, %{sub Int}))"])
         ]
       | Pair (a, b) -> [ (fun () -> [%string "(GPair (%{sub a}, %{sub b}))"]) ]
       | _ -> [])
;;
