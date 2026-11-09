open Ty
open Ctx
open Gen_ty

(* What generated code can use at a point in the program. *)
type env =
  { vars : (string * ty) list
  ; locals : (string * ty) list
    (* Stack-allocated values, which are only matched on or have an immediate
         field read, so none escapes its region. *)
  ; in_try : bool (* whether a handler for [Exit] is around *)
  ; handled_effects : effect_decl list
  ; mutables : (string * ty) list (* [let mutable]s, which no closure can use *)
  ; in_fun : bool (* inside a function, which may be called where order matters *)
  }

let bind env var ty = { env with vars = (var, ty) :: env.vars }
let bind_all env vars = List.fold_left (fun env (var, ty) -> bind env var ty) env vars
let bind_local env var ty = { env with locals = (var, ty) :: env.locals }
let closure env = { env with locals = []; mutables = []; in_fun = true }

(* A closure that escapes may run outside the try blocks and handlers around it. *)
let escape env = { (closure env) with handled_effects = []; in_try = false }

(* A lazy must not perform an effect, as that could leave it unfinished. *)
let lazy_body env = { (escape env) with in_try = env.in_try }

(* Code that cannot raise, perform, tick, or use a local or a mutable, so that
   evaluating it anywhere does not change the output. Generated code only
   mutates values it creates. *)
let pure env =
  { env with
    locals = []
  ; mutables = []
  ; in_try = false
  ; handled_effects = []
  ; in_fun = true
  }
;;

let immediate = function
  | Int | Bool -> true
  | _ -> false
;;

(* Usually a type found by [extract] in a variable in scope, so that eliminators
   use computed values rather than literals. *)
let candidates ctx env extract =
  let all = env.vars @ env.locals in
  let found vars = List.filter_map (fun (_, ty) -> extract ty) vars in
  match found (unused ctx all) with
  | [] -> found all
  | found -> found
;;

(* Extractors for [candidates]. *)
let some_ty ty = Some ty

let lists = function
  | List _ as ty -> Some ty
  | _ -> None
;;

let first_order_ty ty = if first_order ty then Some ty else None

let elem_of = function
  | List elem_ty -> elem_ty
  | _ -> invalid_arg "elem_of"
;;

(* The expression generators one level down. [of_shape] draws the type too;
   [scrutinee] may return a local, and says whether it did. *)
type gen =
  { expr : env -> ty -> string
  ; of_shape : ?candidates:ty list -> ?p:float -> env -> shape -> ty * string
  ; scrutinee :
      ?candidates:ty list
      -> ?alt:(ty -> (unit -> string) option)
      -> env
      -> shape
      -> ty * string * bool
  }
