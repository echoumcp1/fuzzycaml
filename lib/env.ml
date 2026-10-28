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
let bind_all env vars = List.fold_left (fun env (x, t) -> bind env x t) env vars
let bind_local env x t = { env with locals = (x, t) :: env.locals }
let closure env = { env with locals = []; muts = [] }

(* For a function that may be called outside the enclosing handlers. *)
let escape env = { (closure env) with effs = [] }

(* For a lazy, which must not perform an effect, as that could leave it
   unfinished. *)
let lazy_body env = { (escape env) with in_try = env.in_try }

let immediate = function
  | Int | Bool -> true
  | _ -> false
;;

(* Usually a type found by [extract] in a variable in scope, so that eliminators
   use computed values rather than literals. *)
let from_env ctx env extract fallback =
  let all = env.vars @ env.locals in
  let unused = unused ctx all in
  let found vars = List.filter_map (fun (_, t) -> extract t) vars in
  (* Prefer unused variables, so that parameters get used. *)
  match found unused, found all with
  | found, _ when found <> [] && flip ~p:0.7 ctx -> pick ctx found
  | _, found when found <> [] && flip ~p:0.7 ctx -> pick ctx found
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
