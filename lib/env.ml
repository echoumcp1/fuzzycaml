open Hegel
open Ty
open Ctx
open Gen_ty

(* [locals] are OxCaml stack-allocated values. They are only matched on or have
   an immediate field read, never returned, stored or captured. *)
type env =
  { vars : (string * ty) list
  ; locals : (string * ty) list
  ; in_try : bool
  ; effs : (string * ty * ty) list (* effects handled by an enclosing handler *)
  ; muts : (string * ty) list (* [let mutable]s, which no closure can use *)
  }

let bind env x t = { env with vars = (x, t) :: env.vars }
let bind_local env x t = { env with locals = (x, t) :: env.locals }
let closure env = { env with locals = []; muts = [] }

(* For a function that may be called outside the enclosing handlers. *)
let escape env = { (closure env) with effs = [] }

let immediate = function
  | Int | Bool -> true
  | _ -> false
;;

(* Usually a type found by [extract] in a variable in scope, so that eliminators
   use computed values rather than literals. *)
let from_env ctx env extract fallback =
  let all = env.vars @ env.locals in
  let unused = List.filter (fun (x, _) -> not (Hashtbl.mem ctx.used x)) all in
  (* Prefer unused variables, so that parameters get used. *)
  let pick vars = List.filter_map (fun (_, t) -> extract t) vars in
  match pick unused, pick all with
  | [], [] -> fallback ()
  | found, _ :: _ when found <> [] && draw_silent ctx.tc (booleans ~p:0.7 ()) ->
    List.nth found (int_in ctx 0 (List.length found - 1))
  | _, found when found <> [] && draw_silent ctx.tc (booleans ~p:0.7 ()) ->
    List.nth found (int_in ctx 0 (List.length found - 1))
  | _ -> fallback ()
;;

let env_ty ctx env extract = from_env ctx env extract (fun () -> any_ty ctx)

let elem = function
  | List s -> Some s
  | _ -> None
;;

let some_ty t = Some t

let fo_env_ty ctx env =
  from_env ctx env (fun t -> if first_order t then Some t else None) (fun () -> fo_ty ctx)
;;
