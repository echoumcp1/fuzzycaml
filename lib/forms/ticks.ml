open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Env

(* Additions to [ticks] commute, so the total only changes if a compiler drops or repeats
   one. They are only used outside functions and where nothing else can raise or perform,
   so evaluation order cannot change the result. *)
let effectful ctx env ty gen =
  let expr = gen.expr in
  let ticked t () =
    [%string "(ticks := !ticks + %{int_in ctx 1 99#Int}; %{expr env t})"]
  in
  let value = not (restricted ty) in
  [ ticked ty ]
  @ (if value
     then
       [ (fun () ->
           (* The tick belongs to the partial application, so it happens once. *)
           let fn = fresh ctx "g" in
           let param = fresh ctx "x" in
           let int_param = fresh ctx "y" in
           let param_ty, arg =
             gen.of_shape ~candidates:(candidates ctx env some_ty) env (Any value_types)
           in
           let body = expr (bind (bind (closure env) param param_ty) int_param Int) ty in
           [%string
             "(let %{fn} = (ticks := !ticks + %{int_in ctx 1 99#Int}; fun (%{param} : \
              %{param_ty#Ty}) (%{int_param} : int) -> %{body}) %{paren arg} in let _ = \
              %{fn} %{paren (expr env Int)} in %{fn} %{paren (expr env Int)})"])
       ; (fun () ->
           let param = fresh ctx "x" in
           [%string
             "(ignore ((ticks := !ticks + %{int_in ctx 1 99#Int}; fun (%{param} : int) \
              (_ : int) -> %{expr (bind (closure env) param Int) Int}) 0); %{expr env \
              ty})"])
       ]
     else [])
  @
  match ty with
  | Int ->
    [ (fun () -> [%string "(%{ticked Int ()} * 0)"])
    ; (fun () -> [%string "(0 * %{ticked Int ()})"])
    ; (fun () -> [%string "(%{ticked Int ()} land 0)"])
    ; (fun () -> [%string "(%{ticked Int ()} lor (-1))"])
    ; (fun () ->
        let op = pick ctx [ "/"; "mod" ] in
        (* -unsafe drops the zero check unless the divisor is a literal. *)
        let denominator =
          choose
            ctx
            [ (fun () -> "0")
            ; (fun () ->
                [%string "(ticks := !ticks + %{int_in ctx 1 99#Int}; %{nonzero ctx})"])
            ]
        in
        let numerator = choose ctx [ (fun () -> "0"); ticked Int ] in
        [%string
          "(try %{numerator} %{op} %{denominator} with Division_by_zero -> %{expr env \
           Int})"])
    ]
  | Int64 ->
    [ (fun () -> [%string "(Int64.mul %{ticked Int64 ()} 0L)"])
    ; (fun () ->
        let fn = pick ctx [ "Int64.div"; "Int64.rem" ] in
        let denominator =
          choose
            ctx
            [ (fun () -> "0L")
            ; (fun () ->
                let divisor_literal = Literal.show_int64 (nonzero64 ctx) in
                [%string "(ticks := !ticks + %{int_in ctx 1 99#Int}; %{divisor_literal})"])
            ]
        in
        [%string
          "(try %{fn} %{ticked Int64 ()} %{denominator} with Division_by_zero -> %{expr \
           env Int64})"])
    ]
  | _ -> []
;;

let forms ctx env ty gen =
  boost
    (if on "effargs"
     then
       gate
         ((not env.in_try) && (not env.in_fun) && env.handled_effects = [])
         (effectful ctx env ty gen)
     else [])
;;
