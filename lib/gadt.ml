open Ty
open Ctx
open Gen_ty
open Env

let rec gadt ctx env shape g depth =
  let e = g.e in
  let sub sh = gadt ctx env sh g (depth - 1) in
  let fixed t = snd (sub (Is t)) in
  let lit () =
    let t, x = g.free env shape in
    t, [%string "(GLit %{x})"]
  in
  if depth <= 0
  then lit ()
  else
    choose
      ctx
      ([ lit
       ; (fun () ->
           let c = fixed Bool in
           let t, a = sub shape in
           let b = fixed t in
           t, [%string "(GIf (%{c}, %{a}, %{b}))"])
       ; (fun () ->
           match sub (Pair_of (shape, Any fo)) with
           | Pair (a, _), p -> a, [%string "(GFst %{p})"]
           | _ -> assert false)
       ; (fun () ->
           match sub (Pair_of (Any fo, shape)) with
           | Pair (_, b), p -> b, [%string "(GSnd %{p})"]
           | _ -> assert false)
       ]
       @
       match shape with
       | Is Int ->
         [ (fun () -> Int, [%string "(GInt %{e env Int})"])
         ; (fun () ->
             let a = fixed Int in
             let b = fixed Int in
             Int, [%string "(GAdd (%{a}, %{b}))"])
         ]
       | Is Bool ->
         [ (fun () -> Bool, [%string "(GBool %{e env Bool})"])
         ; (fun () ->
             let a = fixed Int in
             let b = fixed Int in
             Bool, [%string "(GLe (%{a}, %{b}))"])
         ]
       | Is (Pair (a, b)) ->
         [ (fun () ->
             let x = fixed a in
             let y = fixed b in
             Pair (a, b), [%string "(GPair (%{x}, %{y}))"])
         ]
       | Pair_of (sa, sb) ->
         [ (fun () ->
             let a, x = sub sa in
             let b, y = sub sb in
             Pair (a, b), [%string "(GPair (%{x}, %{y}))"])
         ]
       | _ -> [])
;;
