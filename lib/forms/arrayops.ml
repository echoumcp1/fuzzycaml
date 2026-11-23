open Config
open Ty
open Ctx
open Env

type container =
  { module_name : string
  ; array_ty : string
  ; elem_ty : ty
  }

let plain elem_ty = { module_name = "Array"; array_ty = show_ty (Arr elem_ty); elem_ty }
let floats = { module_name = "Float.Array"; array_ty = "Float.Array.t"; elem_ty = Float }

(* The array is not bound in [stage_env]: it may be empty, which readers of
   arrays in an environment do not expect. *)
type stage =
  { lets : string
  ; array : string
  ; container : container
  ; stage_env : env
  }

(* A start or length in [0, bound], which every function here accepts. *)
let clamped value bound = [%string "((%{value} land max_int) mod (%{bound} + 1))"]

(* Arrays of these are never flat, though some point to floats. *)
let element ctx =
  pick
    ctx
    ([ Int
     ; Bool
     ; Char
     ; Int64
     ; Option Float
     ; Pair (Float, Int)
     ; Arr Float
     ; Arrow (Int, Float)
     ]
     @ if on "strings" then [ Str ] else [])
;;

(* A fresh array, so that the steps after it may write to it. *)
let source ctx env gen c =
  let expr = gen.expr in
  let m = c.module_name in
  let array = fresh ctx "a" in
  (* Arrays of more than 256 words are allocated in the major heap, where blit and
     fill take other paths in the runtime. *)
  let length () =
    if flip ~p:0.05 ctx
    then [%string "(257 + (%{expr env Int} land 255))"]
    else [%string "(%{expr env Int} land 7)"]
  in
  let value =
    choose
      ctx
      ([ (fun () ->
           let length = length () in
           let elem = expr env c.elem_ty in
           [%string "(%{m}.make %{length} %{elem})"])
       ; (fun () ->
           let length = length () in
           let index = fresh ctx "i" in
           let elem = expr (bind (closure env) index Int) c.elem_ty in
           [%string "(%{m}.init %{length} (fun (%{index} : int) -> %{elem}))"])
       ; (fun () ->
           let elems =
             String.concat "; " (List.init (int_in ctx 1 4) (fun _ -> expr env c.elem_ty))
           in
           [%string "(%{m}.of_list [ %{elems} ])"])
       ]
       @
       if c.module_name = "Array"
       then [ (fun () -> [%string "(Array.copy %{expr env (Arr c.elem_ty)})"]) ]
       else
         [ (fun () ->
             [%string
               "(Float.Array.map_from_array (fun (x : float) -> x) %{expr env (Arr \
                Float)})"])
         ])
  in
  { lets = [%string "let %{array} : %{c.array_ty} = %{value} in "]
  ; array
  ; container = c
  ; stage_env = env
  }
;;

(* Each step writes only to an array it has just made. *)
let step ctx gen stage =
  let expr = gen.expr in
  let { array; container = c; stage_env = env; _ } = stage in
  let m = c.module_name in
  let next = fresh ctx "a" in
  let length = [%string "%{m}.length %{array}"] in
  let elem_var = fresh ctx "x" in
  let copied mutation =
    let lets = [%string "let %{next} = %{m}.copy %{array} in %{mutation}; "] in
    lets, c
  in
  let made value c' = [%string "let %{next} : %{c'.array_ty} = %{value} in "], c' in
  let mapped result_c =
    let body = expr (bind (closure env) elem_var c.elem_ty) result_c.elem_ty in
    [%string "(fun (%{elem_var} : %{c.elem_ty#Ty}) -> %{body})"]
  in
  let lets, c' =
    choose
      ctx
      ([ (fun () ->
           let start = fresh ctx "o" in
           let start_value = clamped (expr env Int) length in
           let sub_length = clamped (expr env Int) [%string "(%{length} - %{start})"] in
           let lets, c' = made [%string "%{m}.sub %{array} %{start} %{sub_length}"] c in
           [%string "let %{start} = %{start_value} in %{lets}"], c')
       ; (fun () ->
           let src = pick ctx [ array; next ] in
           let src_pos = fresh ctx "o" in
           let dst_pos = fresh ctx "o" in
           let src_value = clamped (expr env Int) length in
           let dst_value = clamped (expr env Int) length in
           let count =
             clamped
               (expr env Int)
               [%string "(min (%{length} - %{src_pos}) (%{length} - %{dst_pos}))"]
           in
           copied
             [%string
               "let %{src_pos} = %{src_value} in let %{dst_pos} = %{dst_value} in \
                %{m}.blit %{src} %{src_pos} %{next} %{dst_pos} %{count}"])
       ; (fun () ->
           let start = fresh ctx "o" in
           let count = fresh ctx "o" in
           let start_value = clamped (expr env Int) length in
           let count_value = clamped (expr env Int) [%string "(%{length} - %{start})"] in
           let value = expr env c.elem_ty in
           copied
             [%string
               "let %{start} = %{start_value} in let %{count} = %{count_value} in \
                %{m}.fill %{next} %{start} %{count} %{value}"])
       ; (fun () ->
           if flip ctx
           then made [%string "%{m}.append %{array} %{array}"] c
           else (
             let other = source ctx env gen c in
             let lets, c' = made [%string "%{m}.append %{array} %{other.array}"] c in
             other.lets ^ lets, c'))
       ; (fun () ->
           let other = source ctx env gen c in
           let lets, c' =
             made [%string "%{m}.concat [ %{array}; %{other.array}; %{array} ]"] c
           in
           other.lets ^ lets, c')
       ; (fun () -> made [%string "%{m}.map %{mapped c} %{array}"] c)
       ; (fun () ->
           let index = fresh ctx "i" in
           let body =
             expr (bind (bind (closure env) index Int) elem_var c.elem_ty) c.elem_ty
           in
           made
             [%string
               "%{m}.mapi (fun (%{index} : int) (%{elem_var} : %{c.elem_ty#Ty}) -> \
                %{body}) %{array}"]
             c)
       ; (fun () ->
           let index = fresh ctx "i" in
           copied
             [%string
               "for %{index} = 0 to %{length} - 1 do %{m}.set %{next} %{index} (%{m}.get \
                %{array} (%{length} - 1 - %{index})) done"])
       ; (fun () ->
           let index = fresh ctx "i" in
           let current = [%string "(%{m}.get %{next} %{index})"] in
           let body = expr (bind (bind env index Int) current c.elem_ty) c.elem_ty in
           copied
             [%string
               "for %{index} = 0 to %{length} - 1 do %{m}.set %{next} %{index} %{body} \
                done"])
       ]
       @ (if first_order c.elem_ty
          then [ (fun () -> copied [%string "%{m}.stable_sort compare %{next}"]) ]
          else [])
       @
       match c.module_name, c.elem_ty with
       | "Array", Float ->
         [ (fun () ->
             made [%string "Float.Array.map_from_array %{mapped floats} %{array}"] floats)
         ]
       | "Array", _ ->
         [ (fun () ->
             let floats_c = plain Float in
             made [%string "Array.map %{mapped floats_c} %{array}"] floats_c)
         ]
       | _ ->
         [ (fun () ->
             let floats_c = plain Float in
             made
               [%string "Float.Array.map_to_array %{mapped floats_c} %{array}"]
               floats_c)
         ])
  in
  { lets = stage.lets ^ lets; array = next; container = c'; stage_env = env }
;;

let reduce ctx ty gen { array; container = c; stage_env = env; _ } =
  let expr = gen.expr in
  let m = c.module_name in
  let length = [%string "%{m}.length %{array}"] in
  let elem_var = fresh ctx "x" in
  let acc = fresh ctx "acc" in
  let step_env = bind (bind (closure env) acc ty) elem_var c.elem_ty in
  let general =
    [ (fun () ->
        let step = expr step_env ty in
        let init = expr env ty in
        [%string
          "%{m}.fold_left (fun (%{acc} : %{ty#Ty}) (%{elem_var} : %{c.elem_ty#Ty}) -> \
           %{step}) %{init} %{array}"])
    ; (fun () ->
        let step = expr step_env ty in
        let init = expr env ty in
        [%string
          "%{m}.fold_right (fun (%{elem_var} : %{c.elem_ty#Ty}) (%{acc} : %{ty#Ty}) -> \
           %{step}) %{array} %{init}"])
    ; (fun () ->
        let empty = expr env ty in
        let index = expr env Int in
        let body = expr (bind env elem_var c.elem_ty) ty in
        [%string
          "(if %{length} = 0 then %{empty} else let %{elem_var} = %{m}.get %{array} \
           ((%{index} land max_int) mod %{length}) in %{body})"])
    ; (fun () ->
        let result = fresh ctx "r" in
        let index = fresh ctx "i" in
        let init = expr env ty in
        let body =
          expr
            (bind
               (bind (bind (closure env) [%string "!%{result}"] ty) index Int)
               elem_var
               c.elem_ty)
            ty
        in
        [%string
          "(let %{result} = ref (%{init} : %{ty#Ty}) in %{m}.iteri (fun (%{index} : int) \
           (%{elem_var} : %{c.elem_ty#Ty}) -> %{result} := %{body}) %{array}; \
           !%{result})"])
    ]
  in
  let predicate () =
    let body = expr (bind (closure env) elem_var c.elem_ty) Bool in
    [%string "(fun (%{elem_var} : %{c.elem_ty#Ty}) -> %{body})"]
  in
  let specific =
    match ty with
    | Int -> [ (fun () -> length) ]
    | Float when c.elem_ty = Float ->
      [ (fun () -> [%string "%{m}.fold_left ( +. ) 0. %{array}"]) ]
    | Bool ->
      [ (fun () -> [%string "%{m}.exists %{predicate ()} %{array}"])
      ; (fun () -> [%string "%{m}.for_all %{predicate ()} %{array}"])
      ]
      @
      if first_order c.elem_ty
      then [ (fun () -> [%string "%{m}.mem %{expr env c.elem_ty} %{array}"]) ]
      else []
    | _ -> []
  in
  choose ctx (general @ specific)
;;

let pipeline ctx env ty gen =
  let c = if flip ~p:0.6 ctx then plain Float else plain (element ctx) in
  let c = if c.elem_ty = Float && flip ctx then floats else c in
  let first = source ctx env gen c in
  let last =
    List.fold_left
      (fun stage () -> step ctx gen stage)
      first
      (List.init (int_in ctx 0 3) ignore)
  in
  [%string "(%{last.lets}%{reduce ctx ty gen last})"]
;;

(* A polymorphic helper must check at run time whether its array is flat, unless
   it is inlined or specialized where the element type is known. *)
let polymorphic ctx env ty gen =
  let expr = gen.expr in
  let helper = fresh ctx "h" in
  let body =
    pick
      ctx
      [ "let n = Array.length a in if n = 0 then a else (let k = (k land max_int) mod n \
         in Array.append (Array.sub a k (n - k)) (Array.sub a 0 k))"
      ; "let b = Array.copy a in let n = Array.length b in (if n > 0 then (let k = (k \
         land max_int) mod n in Array.blit b 0 b k (n - k))); b"
      ; "let b = Array.copy a in let n = Array.length b in (if n > 0 then (let i = (k \
         land max_int) mod n in let t = b.(i) in b.(i) <- b.(n - 1 - i); b.(n - 1 - i) \
         <- t)); b"
      ; "let b = Array.append a a in let n = Array.length a in (if n > 0 then Array.fill \
         b ((k land max_int) mod n) n b.(n - 1)); b"
      ; "Array.init (Array.length a) (fun i -> a.((i + (k land max_int) mod \
         (Array.length a)) mod Array.length a))"
      ]
  in
  let attr = pick ctx [ ""; "[@inline]"; "[@inline never]" ] in
  let call () =
    pick
      ctx
      [ helper
      ; [%string "(%{helper} [@inlined never])"]
      ; [%string "(%{helper} [@inlined])"]
      ]
  in
  let apply stage =
    let result = fresh ctx "r" in
    let head = call () in
    let shift = expr stage.stage_env Int in
    { stage with
      lets = stage.lets ^ [%string "let %{result} = %{head} %{stage.array} %{shift} in "]
    ; array = result
    }
  in
  let others = apply (source ctx env gen (plain (element ctx))) in
  let other_result = fresh ctx "y" in
  let other_value = reduce ctx ty gen others in
  let float_env = bind others.stage_env other_result ty in
  let float_stage = apply (source ctx float_env gen (plain Float)) in
  [%string
    "(let%{attr} %{helper} : 'a. 'a array -> int -> 'a array = fun a k -> %{body} in \
     %{others.lets}let %{other_result} : %{ty#Ty} = %{other_value} in \
     %{float_stage.lets}%{reduce ctx ty gen float_stage})"]
;;

(* Erased, the unboxed float array is a float array. *)
let unboxed_floats ctx env gen =
  let expr = gen.expr in
  let count = fresh ctx "n" in
  let array = fresh ctx "u" in
  let shift = fresh ctx "s" in
  let index = fresh ctx "i" in
  let length = expr env Int in
  let init = expr env Float in
  let shift_value = expr env Int in
  let body = expr (bind env index Int) Float in
  let read = expr env Int in
  let array_ty = Arr unboxed_float in
  [%string
    "(let %{count} = 1 + (%{length} land 7) in let %{array} : %{array_ty#Ty} = \
     array_make %{count} (unbox_float %{init}) in let %{shift} = (%{shift_value} land \
     max_int) mod %{count} in for %{index} = 0 to %{count} - 1 do array_set %{array} \
     %{index} (fu_add (array_get %{array} ((%{index} + %{shift}) mod %{count})) \
     (unbox_float %{body})) done; box_float (array_get %{array} ((%{read} land max_int) \
     mod %{count})))"]
;;

let forms ctx env ty gen =
  if on "arrayops" && not (restricted ty)
  then
    boost
      ([ (fun () -> pipeline ctx env ty gen); (fun () -> polymorphic ctx env ty gen) ]
       @ if ty = Float && !ox_mode then [ (fun () -> unboxed_floats ctx env gen) ] else []
      )
  else []
;;
