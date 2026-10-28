open Ty
open Ctx
open Env

(* A term of the prelude's GADT that evaluates to a value of [ty]. *)
let rec gadt ctx env ty e depth =
  let sub t = gadt ctx env t e (depth - 1) in
  let lit () = p "(GLit %s)" (e env ty) in
  if depth <= 0
  then lit ()
  else
    choose
      ctx
      ([ lit; (fun () -> p "(GIf (%s, %s, %s))" (sub Bool) (sub ty) (sub ty))
       ; (fun () -> p "(GFst %s)" (sub (Pair (ty, fo_env_ty ctx env))))
       ; (fun () -> p "(GSnd %s)" (sub (Pair (fo_env_ty ctx env, ty))))
       ]
       @
       match ty with
       | Int ->
         [ (fun () -> p "(GInt %s)" (e env Int))
         ; (fun () -> p "(GAdd (%s, %s))" (sub Int) (sub Int))
         ]
       | Bool ->
         [ (fun () -> p "(GBool %s)" (e env Bool))
         ; (fun () -> p "(GLe (%s, %s))" (sub Int) (sub Int))
         ]
       | Pair (a, b) -> [ (fun () -> p "(GPair (%s, %s))" (sub a) (sub b)) ]
       | _ -> [])
;;
