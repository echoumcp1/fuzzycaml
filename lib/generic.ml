open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Pattern
open Env
open Effects
open Gadt
open Ox
open Stress
open Forms

let generic ctx env ty e =
  let fo = first_order ty in
  let value = not (restricted ty) in
  (* A scrutinee of type [s], sometimes a local (whose components are then also
     local). *)
  let scrutinee env s =
    match List.filter (fun (_, t) -> t = s) env.locals with
    | locals when locals <> [] && flip ~p:0.6 ctx ->
      fst (pick ctx locals), true
    | _ -> e env s, false
  in
  let bind_part local env x t =
    if local && not (immediate t) then bind_local env x t else bind env x t
  in
  let rec_attr () =
    pick
      ctx
      ([ ""; "[@inline never]"; "[@inline always]" ]
       @ if !ox_mode then [ "[@unrolled 2]"; "[@loop always]" ] else [])
  in
  let call_attr go =
    choose
      ctx
      [ (fun () -> go)
      ; (fun () -> p "(%s [@inlined never])" go)
      ; (fun () -> p "(%s [@inlined])" go)
      ]
  in
  [ (fun () -> p "(if %s then %s else %s)" (e env Bool) (e env ty) (e env ty))
  ; (fun () ->
      let s = from_env ctx env some_ty (fun () -> top_ty ctx) in
      let x = fresh ctx "x" in
      p "(let %s : %s = %s in %s)" x (show_ty s) (e env s) (e (bind env x s) ty))
  ; (fun () ->
      let s =
        from_env
          ctx
          env
          (function
            | Arrow (s, r) when r = ty -> Some s
            | _ -> None)
          (fun () -> top_ty ctx)
      in
      p "(%s %s)" (e env (Arrow (s, ty))) (e env s))
  ; (fun () ->
      let s = top_ty ctx in
      let x = fresh ctx "x" in
      p
        "((fun (%s : %s) -> %s) %s)"
        x
        (show_ty s)
        (e (bind (closure env) x s) ty)
        (e env s))
  ; (fun () ->
      let s = env_ty ctx env elem in
      let h = fresh ctx "h" in
      let t = fresh ctx "t" in
      let l, local = scrutinee env (List s) in
      p
        "(match %s with [] -> %s | %s :: %s -> %s)"
        l
        (e env ty)
        h
        t
        (e (bind_part local (bind_part local env h s) t (List s)) ty))
  ; (fun () ->
      let s =
        env_ty ctx env (function
          | Option s -> Some s
          | _ -> None)
      in
      let x = fresh ctx "x" in
      let o, local = scrutinee env (Option s) in
      p
        "(match %s with None -> %s | Some %s -> %s)"
        o
        (e env ty)
        x
        (e (bind_part local env x s) ty))
  ; (fun () ->
      let a, b =
        from_env
          ctx
          env
          (function
            | Pair (a, b) -> Some (a, b)
            | _ -> None)
          (fun () -> any_ty ctx, any_ty ctx)
      in
      let x = fresh ctx "x" in
      let y = fresh ctx "y" in
      let v, local = scrutinee env (Pair (a, b)) in
      p
        "(let (%s, %s) = %s in %s)"
        x
        y
        v
        (e (bind_part local (bind_part local env x a) y b) ty))
  ; (fun () ->
      let go = fresh ctx "go" in
      let n = fresh ctx "n" in
      let acc = fresh ctx "acc" in
      let env = closure env in
      p
        "(let%s rec %s (%s : int) (%s : %s) : %s = if %s <= 0 then %s else %s (%s - 1) \
         %s in %s (%s land 15) %s)"
        (rec_attr ())
        go
        n
        acc
        (show_ty ty)
        (show_ty ty)
        n
        acc
        go
        n
        (e (bind (bind env n Int) acc ty) ty)
        (call_attr go)
        (e env Int)
        (e env ty))
  ; (fun () ->
      let go = fresh ctx "go" in
      let n = fresh ctx "n" in
      let r = fresh ctx "r" in
      let env = closure env in
      p
        "(let%s rec %s (%s : int) : %s = if %s <= 0 then %s else (let %s : %s = %s (%s - \
         1) in %s) in %s (%s land 15))"
        (rec_attr ())
        go
        n
        (show_ty ty)
        n
        (e (bind env n Int) ty)
        r
        (show_ty ty)
        go
        n
        (e (bind (bind env n Int) r ty) ty)
        (call_attr go)
        (e env Int))
  ; (fun () ->
      if on "exits"
      then p "(try %s with Exit -> %s)" (e { env with in_try = true } ty) (e env ty)
      else p "(if %s then %s else %s)" (e env Bool) (e env ty) (e env ty))
  ; (fun () ->
      let s =
        from_env
          ctx
          env
          (function
            | Named _ as t -> Some t
            | _ -> None)
          (fun () -> from_env ctx env some_ty (fun () -> top_ty ctx))
      in
      let v, local = scrutinee env s in
      let variants =
        List.filter_map
          (fun (j, d) ->
             match d with
             | Variant cs -> Some (j, cs)
             | _ -> None)
          (indexed_decls ctx)
      in
      let v =
        match s with
        | Pair (a, b) when (not local) && flip ~p:0.4 ctx ->
          p "%s, %s" (e env a) (e env b)
        | Named k
          when (not local) && List.mem_assoc k variants && flip ~p:0.3 ctx ->
          (* match-in-match: the inner match's input is opaque, so its result
             constructor is unknown, but each arm builds a known one. *)
          let outs = List.assoc k variants in
          let j, ins = pick ctx variants in
          let off = int_in ctx 0 (List.length outs - 1) in
          let arm idx (c, args) =
            let c', args' = List.nth outs ((idx + off) mod List.length outs) in
            p "| %s -> %s" (construct c (List.map (fun _ -> "_") args)) (construct c' (List.map (e env) args'))
          in
          p "(match Sys.opaque_identity %s with %s)" (e env (Named j)) (String.concat " " (List.mapi arm ins))
        | _ -> v
      in
      let arm () =
        let q, bound = pattern ~top:true ctx s 3 ~binds:true in
        let env' = List.fold_left (fun env (x, t) -> bind_part local env x t) env bound in
        let guard =
          if flip ~p:0.3 ctx
          then p " when %s" (e env' Bool)
          else ""
        in
        p "| %s%s -> %s" q guard (e env' ty)
      in
      let arms = List.init (int_in ctx 1 4) (fun _ -> arm ()) in
      let arms =
        String.concat
          " "
          (if (not local) && (not (restricted s)) && on "exits" && flip ~p:0.2 ctx
           then arms @ [ p "| exception Exit -> %s" (e env ty) ]
           else arms)
      in
      if flip ~p:0.6 ctx
      then (
        let x = fresh ctx "m" in
        p "(match %s with %s | %s -> %s)" v arms x (e (bind_part local env x s) ty))
      else
        (* Without a catch-all the match may fail, so a Match_failure handler
           goes around it. *)
        p "(try (match %s with %s) with Match_failure _ -> %s)" v arms (e env ty))
  ]
  @ (if not value
     then []
     else
       [ (fun () ->
           if on "opaque" then p "(Sys.opaque_identity %s)" (e env ty) else e env ty)
       ; (fun () ->
           let s =
             env_ty ctx env (function
               | Pair (a, b) when a = ty -> Some b
               | _ -> None)
           in
           p "(fst %s)" (e env (Pair (ty, s))))
       ; (fun () ->
           let s =
             env_ty ctx env (function
               | Pair (a, b) when b = ty -> Some a
               | _ -> None)
           in
           p "(snd %s)" (e env (Pair (s, ty))))
       ; (fun () ->
           let s = env_ty ctx env elem in
           let acc = fresh ctx "acc" in
           let x = fresh ctx "x" in
           p
             "(List.fold_left (fun (%s : %s) (%s : %s) -> %s) %s %s)"
             acc
             (show_ty ty)
             x
             (show_ty s)
             (e (bind (bind (closure env) acc ty) x s) ty)
             (e env ty)
             (e env (List s)))
       ])
  @ List.concat_map
      (fun (i, decl) ->
         match decl with
         | Record fields ->
           List.filter_map
             (fun (f, t, _) ->
                if t = ty
                then
                  Some
                    (fun () ->
                      (* A local record's field is local unless it is immediate. *)
                      let r =
                        if immediate t
                        then fst (scrutinee env (Named i))
                        else e env (Named i)
                      in
                      p "(%s).%s" r f)
                else None)
             fields
         | URecord fields ->
           List.filter_map
             (fun (f, t) -> if t = ty then Some (fun () -> p "(%s).#%s" (e env (Named i)) f) else None)
             fields
         | Variant _ -> [])
      (indexed_decls ctx)
  (* Reading an array at an in-bounds index. OxCaml arrays hold numbers. *)
  @ (if on "arrays"
        && if !ox_mode then is_num ty || (match ty with Arr _ -> true | _ -> false) else value
     then
       [ (fun () ->
           let a = fresh ctx "a" in
           p "(let %s = %s in array_get %s ((%s land max_int) mod array_length %s))" a (e env (Arr ty)) a (e env Int) a)
       ]
       @
       match ty with
       | Float | Int ->
         [ (fun () ->
             p "(arr_get %s %s %s)" (if ty = Float then "AwFloat" else "AwInt") (e env (Arr ty)) (e env Int))
         ]
       | _ -> []
     else [])
  @ (if !ox_mode then ox_forms ctx env ty e else [])
  @ (if env.in_try
     then [ (fun () -> raise_at ctx ty) ]
     else [])
  @ (if !ox_mode && immediate ty && on "locals"
     then [ (fun () -> local_binding ctx env ty e) ]
     else [])
  @ boost (if value && on "partial" then [ (fun () -> partial ctx env ty e) ] else [])
  @ boost (if fo && ctx.effects <> [] && on "deep" then [ (fun () -> handler ctx env ty e) ] else [])
  @ boost (if fo && ctx.effects <> [] && on "shallow" then [ (fun () -> shallow ctx env ty e) ] else [])
  @ boost (if fo && ctx.effects <> [] && !use_effect_syntax && on "effect_syntax"
     then [ (fun () -> effect_match ctx env ty e) ]
     else [])
  @ boost (if value && on "lazy" then [ (fun () -> lazy_value ctx env ty e) ] else [])
  @ boost (if value && on "recvals" then rec_value ctx env ty e else [])
  @ (if on "strings" then [ (fun () -> str_match ctx env ty e) ] else [])
  @ boost (if fo && on "gadt"
     then
       [ (fun () -> p "(geval %s)" (gadt ctx env ty e 3))
       ; (fun () ->
           match ty with
           | Int | Bool ->
             p "(gbump %s %s)" (gadt ctx env ty e 2) (e env ty)
           | _ -> p "(geval %s)" (gadt ctx env ty e 2))
       ]
     else [])
  @ boost (List.filter_map
      (fun (child, parent) ->
         if Named child = ty
         then Some (fun () -> p "(%s : t%d :> t%d)" (e env (Named parent)) parent child)
         else None)
      !poly_parent)
  @ boost (if immediate ty && on "atomics" then [ (fun () -> local_atomic ctx env ty e) ] else [])
  @ (if fo then [ (fun () -> pressure ctx env ty e) ] else [])
  @ (if value && on "manyargs" then [ (fun () -> many_args ctx env ty e) ] else [])
  @ boost (if value && on "gc" then [ (fun () -> gc ctx env ty e) ] else [])
  @ boost (if value && on "exns" then [ (fun () -> local_exn ctx env ty e) ] else [])
  (* Both branches are equal, so the optimiser can join them. *)
  @ boost
      (if on "samebranch"
       then [ (fun () -> let c = e env Bool in let a = e env ty in p "(if %s then %s else %s)" c a a) ]
       else [])
  @
  if (not fo) || not (on "loops")
  then []
  else
    [ (fun () ->
        let r = fresh ctx "r" in
        let i = fresh ctx "i" in
        p
          "(let %s = ref (%s : %s) in for %s = 0 to (%s land 7) do %s := %s done; !%s)"
          r
          (e env ty)
          (show_ty ty)
          i
          (e env Int)
          r
          (e (bind (bind env (p "!%s" r) ty) i Int) ty)
          r)
    ; (fun () ->
        let r = fresh ctx "r" in
        let k = fresh ctx "k" in
        let lim = fresh ctx "lim" in
        let env' = bind env (p "!%s" r) ty in
        p
          "(let %s = ref (%s : %s) in let %s = ref 0 in let %s = %s land 7 in while !%s < %s && \
           %s do %s := %s; incr %s done; !%s)"
          r
          (e env ty)
          (show_ty ty)
          k
          lim
          (e env Int)
          k
          lim
          (e env' Bool)
          r
          (e (bind env' (p "!%s" k) Int) ty)
          k
          r)
    ; (fun () ->
        let a = fresh ctx "a" in
        let i = fresh ctx "i" in
        let get = p "%s.(%s mod Array.length %s)" a i a in
        p
          "(let %s = Array.make (1 + (%s land 7)) %s in for %s = 0 to (%s land 7) do \
           %s.((%s land max_int) mod Array.length %s) <- %s done; Array.fold_left (fun \
           (_ : %s) (x : %s) -> x) %s.(0) %s)"
          a
          (e env Int)
          (e env ty)
          i
          (e env Int)
          a
          (e (bind env i Int) Int)
          a
          (e (bind (bind env get ty) i Int) ty)
          (show_ty ty)
          (show_ty ty)
          a
          a)
    ]
;;
