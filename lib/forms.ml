open Ty
open Ctx
open Gen_ty
open Env

let partial ctx env ty e =
  let f = fresh ctx "f" in
  let n = int_in ctx 1 4 in
  let env = closure env in
  let params, body_env =
    List.fold_left
      (fun (params, env) i ->
         let x = fresh ctx "a" in
         let kind =
           if i = n - 1
           then `Pos
           else choose ctx [ (fun () -> `Pos); (fun () -> `Lab); (fun () -> `Opt) ]
         in
         let t = if kind = `Pos then top_ty ctx else any_ty ctx in
         let decl =
           match kind with
           | `Pos -> [%string "(%{x} : %{t#Ty})"]
           | `Lab -> [%string "~(%{x} : %{t#Ty})"]
           | `Opt -> [%string "?(%{x} : %{t#Ty} = %{e env t})"]
         in
         params @ [ x, t, kind, decl ], bind env x t)
      ([], env)
      (List.init n Fun.id)
  in
  let arg ~omittable (x, t, kind, _) =
    match kind with
    | `Pos -> Some (true, paren (e env t))
    | `Lab -> Some (false, [%string "~%{x}:(%{e env t})"])
    | `Opt ->
      choose
        ctx
        ([ (fun () -> Some (false, [%string "~%{x}:(%{e env t})"]))
         ; (fun () -> Some (false, [%string "?%{x}:(Some %{e env t})"]))
         ; (fun () -> Some (false, [%string "?%{x}:None"]))
         ]
         @ if omittable then [ (fun () -> None) ] else [])
  in
  (* An optional argument can only be left out before a positional one. *)
  let rec args = function
    | [] -> []
    | param :: rest ->
      let omittable = List.exists (fun (_, _, kind, _) -> kind = `Pos) rest in
      let a = arg ~omittable param in
      Option.to_list a @ args rest
  in
  (* Labeled arguments commute; positional ones keep their order. *)
  let shuffle args =
    let moved, kept =
      List.partition (fun (pos, _) -> (not pos) && flip ~p:0.3 ctx) args
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
  let attr = pick ctx [ ""; "[@inline never]"; "[@inline]" ] in
  let head =
    choose
      ctx
      [ (fun () -> f)
      ; (fun () -> [%string "(%{f} [@inlined never])"])
      ; (fun () -> [%string "(Sys.opaque_identity %{f})"])
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
             [ (fun () -> [%string "(%{acc} %{chunk})"])
             ; (fun () -> [%string "((Sys.opaque_identity %{acc}) %{chunk})"])
             ; (fun () ->
                 let q = fresh ctx "q" in
                 [%string "(let %{q} = %{acc} in %{q} %{chunk})"])
             ])
        [%string "(%{head} %{first})"]
        rest
  in
  let decls = String.concat " " (List.map (fun (_, _, _, decl) -> decl) params) in
  [%string "(let%{attr} %{f} %{decls} : %{ty#Ty} = %{e body_env ty} in %{call})"]
;;

let atomic_op ctx env a ty e =
  (* let-bound because argument evaluation order is unspecified and differs between ocamlc
     and ocamlopt *)
  let cas seen v =
    let x = fresh ctx "c"
    and y = fresh ctx "c" in
    [%string
      "(let %{x} = %{seen} in let %{y} = %{v} in Atomic.compare_and_set %{a} %{x} %{y})"]
  in
  (* keeps the old value live, so it may be spilled *)
  let keep_old op v =
    let o = fresh ctx "old" in
    let use_old = e (bind env o ty) ty in
    [%string "(let %{o} = %{op} %{a} %{v} in ignore (Sys.opaque_identity %{use_old}))"]
  in
  choose
    ctx
    ([ (fun () -> [%string "Atomic.set %{a} %{e env ty}"])
     ; (fun () -> [%string "ignore (Atomic.exchange %{a} %{e env ty})"])
     ; (fun () -> keep_old "Atomic.exchange" (e env ty))
     ; (fun () ->
         let get = [%string "Atomic.get %{a}"] in
         [%string "ignore %{cas get (e env ty)}"])
     ; (fun () -> [%string "ignore %{cas (e env ty) (e env ty)}"])
     ; (fun () ->
         p
           "(if %s then %s)"
           (cas (e env ty) (e env ty))
           (match ty with
            | Int -> [%string "Atomic.incr %{a}"]
            | _ -> [%string "Atomic.set %{a} (not (Atomic.get %{a}))"]))
     ]
     @
     match ty with
     | Int ->
       [ (fun () -> [%string "ignore (Atomic.fetch_and_add %{a} %{e env Int})"])
       ; (fun () -> keep_old "Atomic.fetch_and_add" (e env Int))
       ; (fun () -> [%string "Atomic.incr %{a}"])
       ; (fun () -> [%string "Atomic.decr %{a}"])
       ]
     | _ -> [])
;;

(* Atomics hold an int or a bool, so compare_and_set's physical equality behaves the same
   on every backend. *)
let local_atomic ctx env ty e =
  let a = fresh ctx "at" in
  let i = fresh ctx "i" in
  let body = bind (bind env [%string "(Atomic.get %{a})"] ty) i Int in
  let ops = List.init (int_in ctx 1 3) (fun _ -> atomic_op ctx body a ty e) in
  let ops = String.concat "; " ops in
  [%string
    "(let %{a} = Atomic.make %{e env ty} in for %{i} = 0 to (%{e env Int} land 7) do \
     %{ops} done; Atomic.get %{a})"]
;;

let local_exn ctx env ty e =
  let x = fresh ctx "X" in
  let th = fresh ctx "th" in
  let b = fresh ctx "b" in
  let v = fresh ctx "v" in
  let cb = fresh ctx "c" in
  let cv = fresh ctx "c" in
  let s = fo_env_ty ctx env in
  let env = closure env in
  let handler = e (bind env v s) ty in
  let arg = e env s in
  let cond = e env Bool in
  let no_raise = e (bind (bind env b Bool) v s) ty in
  let raise = pick ctx [ "raise"; "raise_notrace" ] in
  let attr = pick ctx [ ""; "[@inline never]" ] in
  [%string
    "(let exception %{x} of %{s#Ty} in let%{attr} %{th} (%{b} : bool) (%{v} : %{s#Ty}) : \
     %{ty#Ty} = if %{b} then %{raise} (%{x} %{v}) else %{no_raise} in let %{cb} = \
     %{cond} in let %{cv} = %{arg} in try %{th} %{cb} %{cv} with %{x} %{v} -> \
     %{handler})"]
;;

let lazy_value ctx env ty e =
  let s =
    from_env
      ctx
      env
      (fun t -> if restricted t then None else Some t)
      (fun () -> any_ty ctx)
  in
  let l = fresh ctx "lz" in
  let x = fresh ctx "x" in
  let body = e (lazy_body env) s in
  choose
    ctx
    [ (fun () ->
        let force = [%string "(Lazy.force %{l})"] in
        [%string "(let %{l} = lazy %{body} in %{e (bind env force s) ty})"])
    ; (fun () ->
        [%string "(match lazy %{body} with lazy %{x} -> %{e (bind env x s) ty})"])
    ; (fun () ->
        [%string "(Lazy.force (Lazy.from_fun (fun () -> %{e (lazy_body env) ty})))"])
    ]
;;

let rec_value ctx env ty e =
  let f = fresh ctx "f" in
  let n = fresh ctx "n" in
  let body env = e (bind (closure env) n Int) ty in
  [ (fun () ->
      let l = fresh ctx "lz" in
      [%string
        "(let rec %{l} : %{ty#Ty} Lazy.t = lazy %{e (lazy_body env) ty} and %{f} : int \
         -> %{ty#Ty} = fun %{n} -> if %{n} <= 0 then Lazy.force %{l} else %{f} (%{n} - \
         1) in %{f} (%{e env Int} land 7))"])
  ; (fun () ->
      let v = fresh ctx "v" in
      let pr = fresh ctx "pr" in
      [%string
        "(let %{v} : %{ty#Ty} = %{e env ty} in let rec %{pr} = (%{f}, %{v}) and %{f} : \
         int -> %{ty#Ty} = fun %{n} -> if %{n} <= 0 then snd %{pr} else (fst %{pr}) \
         (%{n} - 1) in (fst %{pr}) (%{e env Int} land 7))"])
  ; (fun () ->
      let g = fresh ctx "g" in
      [%string
        "(let rec %{f} (%{n} : int) : %{ty#Ty} = if %{n} <= 0 then %{body env} else %{g} \
         (%{n} - 1) and %{g} (%{n} : int) : %{ty#Ty} = if %{n} <= 0 then %{body env} \
         else %{f} (%{n} - 1) in %{f} (%{e env Int} land 15))"])
  ]
  @
  match ty with
  | List t ->
    [ (fun () ->
        let a = fresh ctx "a" in
        let b = fresh ctx "b" in
        let c = fresh ctx "c" in
        [%string
          "(let %{a} : %{t#Ty} = %{e env t} in let %{b} : %{t#Ty} = %{e env t} in let \
           rec %{c} = %{a} :: %{b} :: %{c} in take (%{e env Int} land 15) %{c})"])
    ]
  | _ -> []
;;

let tmc ctx env t e =
  let go = fresh ctx "go" in
  let n = fresh ctx "n" in
  let x = fresh ctx "x" in
  let env' = bind (closure env) n Int in
  let call = [%string "%{go} (%{n} - 1)"] in
  let cons () = [%string "(let %{x} : %{t#Ty} = %{e env' t} in %{x} :: %{call})"] in
  let step =
    choose
      ctx
      [ cons
      ; (fun () -> [%string "(if %{e env' Bool} then %{cons ()} else %{call})"])
      ; (fun () ->
          let h = fresh ctx "h" in
          [%string
            "(match %{e env' (List t)} with [] -> %{call} | %{h} :: _ -> %{h} :: %{call})"])
      ; (fun () ->
          let y = fresh ctx "y" in
          [%string
            "(let %{x} : %{t#Ty} = %{e env' t} in let %{y} : %{t#Ty} = %{e env' t} in \
             %{x} :: %{y} :: %{call})"])
      ]
  in
  [%string
    "(let[@tail_mod_cons] rec %{go} (%{n} : int) : %{(List t)#Ty} = if %{n} <= 0 then \
     %{e env' (List t)} else %{step} in (%{go}[@tailcall false]) (%{e env Int} land 15))"]
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
        let n = Trace.unbounded ctx.tc in
        paren (string_of_int (if n = 0 then 3 else n)))
    ]
;;

(* Additions to [ticks] commute, so the total only changes if a compiler drops or repeats
   one. They are only used outside functions and where nothing else can raise or perform,
   so evaluation order cannot change the result. *)
let effectful ctx env ty e =
  let tick t () = [%string "(ticks := !ticks + %{int_in ctx 1 99#Int}; %{e env t})"] in
  let value = not (restricted ty) in
  [ tick ty ]
  @ (if value
     then
       [ (fun () ->
           (* the tick belongs to the partial application, so it happens once *)
           let g = fresh ctx "g" in
           let x = fresh ctx "x" in
           let y = fresh ctx "y" in
           let s = env_ty ctx env some_ty in
           let body = e (bind (bind (closure env) x s) y Int) ty in
           [%string
             "(let %{g} = (ticks := !ticks + %{int_in ctx 1 99#Int}; fun (%{x} : \
              %{s#Ty}) (%{y} : int) -> %{body}) %{paren (e env s)} in let _ = %{g} \
              %{paren (e env Int)} in %{g} %{paren (e env Int)})"])
       ; (fun () ->
           let x = fresh ctx "x" in
           [%string
             "(ignore ((ticks := !ticks + %{int_in ctx 1 99#Int}; fun (%{x} : int) (_ : \
              int) -> %{e (bind (closure env) x Int) Int}) 0); %{e env ty})"])
       ]
     else [])
  @
  match ty with
  | Int ->
    [ (fun () -> [%string "(%{tick Int ()} * 0)"])
    ; (fun () -> [%string "(0 * %{tick Int ()})"])
    ; (fun () -> [%string "(%{tick Int ()} land 0)"])
    ; (fun () -> [%string "(%{tick Int ()} lor (-1))"])
    ; (fun () ->
        let op = pick ctx [ "/"; "mod" ] in
        (* -unsafe drops the zero check unless the divisor is a literal *)
        let d =
          choose
            ctx
            [ (fun () -> "0")
            ; (fun () ->
                [%string "(ticks := !ticks + %{int_in ctx 1 99#Int}; %{nonzero ctx})"])
            ]
        in
        let n = choose ctx [ (fun () -> "0"); tick Int ] in
        [%string "(try %{n} %{op} %{d} with Division_by_zero -> %{e env Int})"])
    ]
  | Int64 ->
    [ (fun () -> [%string "(Int64.mul %{tick Int64 ()} 0L)"])
    ; (fun () ->
        let f = pick ctx [ "Int64.div"; "Int64.rem" ] in
        let d =
          choose
            ctx
            [ (fun () -> "0L")
            ; (fun () ->
                let k = Literal.int64_lit (nonzero64 ctx) in
                [%string "(ticks := !ticks + %{int_in ctx 1 99#Int}; %{k})"])
            ]
        in
        [%string
          "(try %{f} %{tick Int64 ()} %{d} with Division_by_zero -> %{e env Int64})"])
    ]
  | _ -> []
;;
