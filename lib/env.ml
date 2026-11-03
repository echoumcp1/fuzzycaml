open Ty
open Ctx
open Gen_ty

(* Locals are only matched on or have an immediate field read, so none escapes its region.
   *)
type env =
  { vars : (string * ty) list
  ; locals : (string * ty) list
  ; in_try : bool
  ; effs : (string * ty * ty) list
  ; muts : (string * ty) list (* [let mutable]s, which no closure can use *)
  ; in_fun : bool (* inside a function, which may be called where order matters *)
  }

let bind env x t = { env with vars = (x, t) :: env.vars }
let bind_all env vars = List.fold_left (fun env (x, t) -> bind env x t) env vars
let bind_local env x t = { env with locals = (x, t) :: env.locals }
let closure env = { env with locals = []; muts = []; in_fun = true }
let escape env = { (closure env) with effs = [] }

(* A lazy must not perform an effect, as that could leave it unfinished. *)
let lazy_body env = { (escape env) with in_try = env.in_try }

let immediate = function
  | Int | Bool -> true
  | _ -> false
;;

(* Usually a type found by [extract] in a variable in scope, so that eliminators
   use computed values rather than literals. *)
let candidates ctx env extract =
  let all = env.vars @ env.locals in
  let found vars = List.filter_map (fun (_, t) -> extract t) vars in
  match found (unused ctx all) with
  | [] -> found all
  | found -> found
;;

let some_ty t = Some t

let lists = function
  | List _ as t -> Some t
  | _ -> None
;;

let elem_of = function
  | List s -> s
  | _ -> invalid_arg "elem_of"
;;

let first_order_ty t = if first_order t then Some t else None

(* [e] at a fixed type; [free] draws the type, preferring [candidates];
   [scrutinee] may be a local variable or [alt]'s expression instead. *)
type gen =
  { e : env -> ty -> string
  ; free : ?candidates:ty list -> ?p:float -> env -> shape -> ty * string
  ; scrutinee :
      ?candidates:ty list
      -> ?alt:(ty -> (unit -> string) option)
      -> env
      -> shape
      -> ty * string * bool
  }
