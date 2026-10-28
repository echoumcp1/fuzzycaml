open Hegel
open Ty
open Ctx
open Gen_ty
open Env

(* A local function with positional, labelled and optional parameters, applied
   all at once or in several steps. *)
let partial ctx env ty e =
  let f = fresh ctx "f" in
  let n = int_in ctx 1 4 in
  let env = closure env in
  let params, body_env =
    List.fold_left
      (fun (params, env) i ->
         let x = fresh ctx "a" in
         let kind =
           if i = n - 1 then `Pos else choose ctx [ (fun () -> `Pos); (fun () -> `Lab); (fun () -> `Opt) ]
         in
         let t = if kind = `Pos then top_ty ctx else any_ty ctx in
         let decl =
           match kind with
           | `Pos -> p "(%s : %s)" x (show_ty t)
           | `Lab -> p "~(%s : %s)" x (show_ty t)
           | `Opt -> p "?(%s : %s = %s)" x (show_ty t) (e env t)
         in
         params @ [ (x, t, kind, decl) ], bind env x t)
      ([], env)
      (List.init n Fun.id)
  in
  let arg ~omittable (x, t, kind, _) =
    match kind with
    | `Pos -> Some (true, paren (e env t))
    | `Lab -> Some (false, p "~%s:(%s)" x (e env t))
    | `Opt ->
      choose
        ctx
        ([ (fun () -> Some (false, p "~%s:(%s)" x (e env t)))
         ; (fun () -> Some (false, p "?%s:(Some %s)" x (e env t)))
         ; (fun () -> Some (false, p "?%s:None" x))
         ]
         @ if omittable then [ (fun () -> None) ] else [])
  in
  (* An optional argument can only be left out before a positional one. *)
  let rec args = function
    | [] -> []
    | param :: rest ->
      let omittable = List.exists (fun (_, _, k, _) -> k = `Pos) rest in
      let a = arg ~omittable param in
      Option.to_list a @ args rest
  in
  (* Labelled arguments commute; positional ones keep their order. *)
  let shuffle args =
    let moved, kept =
      List.partition (fun (pos, _) -> (not pos) && draw_silent ctx.tc (booleans ~p:0.3 ())) args
    in
    String.concat " " (List.map snd (kept @ moved))
  in
  let rec chunks = function
    | [] -> []
    | params ->
      let k = int_in ctx 1 (List.length params) in
      let here = List.filteri (fun i _ -> i < k) params in
      let rest = List.filteri (fun i _ -> i >= k) params in
      shuffle (args here) :: chunks rest
  in
  let attr = choose ctx [ (fun () -> ""); (fun () -> "[@inline never]"); (fun () -> "[@inline]") ] in
  let head =
    choose
      ctx
      [ (fun () -> f)
      ; (fun () -> p "(%s [@inlined never])" f)
      ; (fun () -> p "(Sys.opaque_identity %s)" f)
      ]
  in
  let call =
    match chunks params with
    | [] -> assert false
    | first :: rest ->
      List.fold_left
        (fun acc chunk ->
           choose
             ctx
             [ (fun () -> p "(%s %s)" acc chunk)
             ; (fun () -> p "((Sys.opaque_identity %s) %s)" acc chunk)
             ; (fun () ->
                 let q = fresh ctx "q" in
                 p "(let %s = %s in %s %s)" q acc q chunk)
             ])
        (p "(%s %s)" head first)
        rest
  in
  p
    "(let%s %s %s : %s = %s in %s)"
    attr
    f
    (String.concat " " (List.map (fun (_, _, _, d) -> d) params))
    (show_ty ty)
    (e body_env ty)
    call
;;

let atomic_op ctx env a ty e =
  (* let-bound because argument evaluation order is unspecified and differs between ocamlc and ocamlopt *)
  let cas seen v =
    let x = fresh ctx "c" and y = fresh ctx "c" in
    p "(let %s = %s in let %s = %s in Atomic.compare_and_set %s %s %s)" x seen y v a x y
  in
  (* keeps the old value live, so it may be spilled *)
  let keep_old op v =
    let o = fresh ctx "old" in
    p "(let %s = %s %s %s in ignore (Sys.opaque_identity %s))" o op a v (e (bind env o ty) ty)
  in
  choose
    ctx
    ([ (fun () -> p "Atomic.set %s %s" a (e env ty))
     ; (fun () -> p "ignore (Atomic.exchange %s %s)" a (e env ty))
     ; (fun () -> keep_old "Atomic.exchange" (e env ty))
     ; (fun () -> p "ignore %s" (cas (p "Atomic.get %s" a) (e env ty)))
     ; (fun () -> p "ignore %s" (cas (e env ty) (e env ty)))
     ; (fun () ->
         p
           "(if %s then %s)"
           (cas (e env ty) (e env ty))
           (match ty with
            | Int -> p "Atomic.incr %s" a
            | _ -> p "Atomic.set %s (not (Atomic.get %s))" a a))
     ]
     @
     match ty with
     | Int ->
       [ (fun () -> p "ignore (Atomic.fetch_and_add %s %s)" a (e env Int))
       ; (fun () -> keep_old "Atomic.fetch_and_add" (e env Int))
       ; (fun () -> p "Atomic.incr %s" a)
       ; (fun () -> p "Atomic.decr %s" a)
       ]
     | _ -> [])
;;

(* A local atomic, updated in a loop and then read. It holds an int or a bool,
   so compare_and_set's physical equality behaves the same on every backend. *)
let local_atomic ctx env ty e =
  let a = fresh ctx "at" in
  let i = fresh ctx "i" in
  let body = bind (bind env (p "(Atomic.get %s)" a) ty) i Int in
  let ops = List.init (int_in ctx 1 3) (fun _ -> atomic_op ctx body a ty e) in
  p
    "(let %s = Atomic.make %s in for %s = 0 to (%s land 7) do %s done; Atomic.get %s)"
    a
    (e env ty)
    i
    (e env Int)
    (String.concat "; " ops)
    a
;;

(* A local exception carrying a value, raised from a function and caught by
   its caller. *)
let local_exn ctx env ty e =
  let x = fresh ctx "X" in
  let th = fresh ctx "th" in
  let b = fresh ctx "b" in
  let v = fresh ctx "v" in
  let cb = fresh ctx "c" in
  let cv = fresh ctx "c" in
  let s = fo_env_ty ctx env in
  let env = closure env in
  p
    "(let exception %s of %s in let%s %s (%s : bool) (%s : %s) : %s = if %s then %s (%s \
     %s) else %s in let %s = %s in let %s = %s in try %s %s %s with %s %s -> %s)"
    x
    (show_ty s)
    (choose ctx [ (fun () -> ""); (fun () -> "[@inline never]") ])
    th
    b
    v
    (show_ty s)
    (show_ty ty)
    b
    (choose ctx [ (fun () -> "raise"); (fun () -> "raise_notrace") ])
    x
    v
    (e (bind (bind env b Bool) v s) ty)
    cb
    (e env Bool)
    cv
    (e env s)
    th
    cb
    cv
    x
    v
    (e (bind env v s) ty)
;;

(* A deferred computation, forced where its value is used. *)
let lazy_value ctx env ty e =
  let s = from_env ctx env (fun t -> if restricted t then None else Some t) (fun () -> any_ty ctx) in
  let l = fresh ctx "lz" in
  let x = fresh ctx "x" in
  (* No effect is performed inside a lazy, since it could leave the lazy
     unfinished. *)
  let body = e { (escape env) with in_try = env.in_try } s in
  choose
    ctx
    [ (fun () ->
        p
          "(let %s = lazy %s in %s)"
          l
          body
          (e (bind env (p "(Lazy.force %s)" l) s) ty))
    ; (fun () -> p "(match lazy %s with lazy %s -> %s)" body x (e (bind env x s) ty))
    ; (fun () -> p "(Lazy.force (Lazy.from_fun (fun () -> %s)))" (e { (escape env) with in_try = env.in_try } ty))
    ]
;;

(* Recursive value definitions: a cyclic list, and lazies, tuples and
   functions that refer to each other. *)
let rec_value ctx env ty e =
  let f = fresh ctx "f" in
  let n = fresh ctx "n" in
  let body env = e (bind (closure env) n Int) ty in
  [ (fun () ->
      let l = fresh ctx "lz" in
      (* no effect inside the lazy, as in [lazy_value] *)
      p
        "(let rec %s : %s Lazy.t = lazy %s and %s : int -> %s = fun %s -> if %s <= 0 \
         then Lazy.force %s else %s (%s - 1) in %s (%s land 7))"
        l
        (show_ty ty)
        (e { (escape env) with in_try = env.in_try } ty)
        f
        (show_ty ty)
        n
        n
        l
        f
        n
        f
        (e env Int))
  ; (fun () ->
      let v = fresh ctx "v" in
      let pr = fresh ctx "pr" in
      p
        "(let %s : %s = %s in let rec %s = (%s, %s) and %s : int -> %s = fun %s -> if %s \
         <= 0 then snd %s else (fst %s) (%s - 1) in (fst %s) (%s land 7))"
        v
        (show_ty ty)
        (e env ty)
        pr
        f
        v
        f
        (show_ty ty)
        n
        n
        pr
        pr
        n
        pr
        (e env Int))
  ; (fun () ->
      let g = fresh ctx "g" in
      p
        "(let rec %s (%s : int) : %s = if %s <= 0 then %s else %s (%s - 1) and %s (%s : \
         int) : %s = if %s <= 0 then %s else %s (%s - 1) in %s (%s land 15))"
        f
        n
        (show_ty ty)
        n
        (body env)
        g
        n
        g
        n
        (show_ty ty)
        n
        (body env)
        f
        n
        f
        (e env Int))
  ]
  @
  match ty with
  | List t ->
    [ (fun () ->
        let a = fresh ctx "a" in
        let b = fresh ctx "b" in
        let c = fresh ctx "c" in
        p
          "(let %s : %s = %s in let %s : %s = %s in let rec %s = %s :: %s :: %s in take \
           (%s land 15) %s)"
          a
          (show_ty t)
          (e env t)
          b
          (show_ty t)
          (e env t)
          c
          a
          b
          c
          (e env Int)
          c)
    ]
  | _ -> []
;;

(* A [@tail_mod_cons] list builder with its recursive call under a constructor.
   *)
let tmc ctx env t e =
  let go = fresh ctx "go" in
  let n = fresh ctx "n" in
  let x = fresh ctx "x" in
  let env' = bind (closure env) n Int in
  let call = p "%s (%s - 1)" go n in
  let cons () = p "(let %s : %s = %s in %s :: %s)" x (show_ty t) (e env' t) x call in
  let step =
    choose
      ctx
      [ cons
      ; (fun () -> p "(if %s then %s else %s)" (e env' Bool) (cons ()) call)
      ; (fun () ->
          let h = fresh ctx "h" in
          p "(match %s with [] -> %s | %s :: _ -> %s :: %s)" (e env' (List t)) call h h call)
      ; (fun () ->
          let y = fresh ctx "y" in
          p
            "(let %s : %s = %s in let %s : %s = %s in %s :: %s :: %s)"
            x
            (show_ty t)
            (e env' t)
            y
            (show_ty t)
            (e env' t)
            x
            y
            call)
      ]
  in
  p
    "(let[@tail_mod_cons] rec %s (%s : int) : %s = if %s <= 0 then %s else %s in \
     (%s[@tailcall false]) (%s land 15))"
    go
    n
    (show_ty (List t))
    n
    (e env' (List t))
    step
    go
    (e env Int)
;;

let nonzero64 ctx =
  choose
    ctx
    [ (fun () -> 1L)
    ; (fun () -> -1L)
    ; (fun () -> Int64.shift_left 1L (int_in ctx 0 62))
    ; (fun () -> Int64.of_int (int_in ctx 2 1000))
    ; (fun () -> Int64.min_int)
    ; (fun () -> Int64.of_int (-int_in ctx 2 1000))
    ]
;;

let nonzero ctx =
  choose
    ctx
    [ (fun () -> "1")
    ; (fun () -> "(-1)")
    ; (fun () -> "2")
    ; (fun () -> paren (string_of_int (1 lsl int_in ctx 0 61)))
    ; (fun () ->
        let n = int_in ctx (-1000) 1000 in
        paren (string_of_int (if n = 0 then 7 else n)))
    ; (fun () -> "max_int")
    ; (fun () -> "min_int")
    ; (fun () ->
        let n = draw_silent ctx.tc (integers ()) in
        paren (string_of_int (if n = 0 then 3 else n)))
    ]
;;
