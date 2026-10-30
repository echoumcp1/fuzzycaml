open Config
open Ty
open Ctx
open Gen_ty
open Literal

let gen_decl ctx =
  if on "records" && flip ctx
  then (
    let all_float = flip ~p:0.3 ctx in
    let float = if !ox_mode && flip ctx then float_u else Float in
    let unboxed () = if on "numbers" then U (pick ctx all_ub) else float_u in
    Record
      (repeat ctx 1 4 (fun _ ->
         let f = fresh ctx "f" in
         let t =
           if all_float
           then float
           else if !ox_mode && flip ~p:0.25 ctx
           then unboxed ()
           else fo_ty ctx
         in
         f, t, flip ~p:0.3 ctx)))
  else (
    let poly = (not !ox_mode) && on "poly" && flip ~p:0.35 ctx in
    let own () =
      repeat ctx 1 4 (fun _ ->
        let c = fresh ctx (if poly then "`C" else "C") in
        c, repeat ctx 0 3 (fun _ -> fo_ty ctx))
    in
    let polys =
      List.filter_map
        (fun (j, d) ->
           match d with
           | Variant ((c, _) :: _ as cs) when c.[0] = '`' -> Some (j, cs)
           | _ -> None)
        (indexed_decls ctx)
    in
    if poly && polys <> [] && flip ctx
    then (
      let j, inherited = pick ctx polys in
      poly_parent := (Array.length ctx.decls, j) :: !poly_parent;
      Variant (inherited @ own ()))
    else Variant (own ()))
;;

let small_int ctx = paren (string_of_int (int_in ctx (-2) 5))

let pattern_int ctx =
  choose
    ctx
    [ (fun () -> "0")
    ; (fun () -> small_int ctx)
    ; (fun () -> small_int ctx)
    ; (fun () -> "1")
    ; (fun () -> "(-1)")
    ; (fun () -> paren (string_of_int (int_in ctx (-100) 100)))
    ; (fun () -> paren (string_of_int (1 lsl int_in ctx 0 61)))
    ; (fun () -> "4611686018427387903")
    ]
;;

(* Both sides of an or-pattern must bind the same variables, so [~binds:false] binds none.
   *)
let rec pattern ?(top = false) ctx ty depth ~binds =
  let none s = s, [] in
  let var () =
    if binds
    then (
      let x = fresh ctx "q" in
      x, [ x, ty ])
    else none "_"
  in
  let sub t = pattern ctx t (depth - 1) ~binds in
  let structural =
    match ty with
    | Int -> [ (fun () -> none (pattern_int ctx)) ]
    | Bool -> [ (fun () -> none "true"); (fun () -> none "false") ]
    | Char ->
      [ (fun () -> none (char_literal ctx))
      ; (fun () ->
          let a = int_in ctx 0 255 in
          let b = int_in ctx a (min 255 (a + int_in ctx 0 30)) in
          none (p "(%C .. %C)" (Char.chr a) (Char.chr b)))
      ; (fun () ->
          let a = int_in ctx (Char.code 'a') (Char.code 'h') in
          let b = int_in ctx a (Char.code 'h') in
          none (p "(%C .. %C)" (Char.chr a) (Char.chr b)))
      ]
    | Int64 ->
      [ (fun () ->
          none
            (choose
               ctx
               [ (fun () -> int64_lit (Int64.of_int (int_in ctx (-2) 5)))
               ; (fun () -> "0L")
               ; (fun () -> "9223372036854775807L")
               ; (fun () -> int64_lit (Int64.shift_left 1L (int_in ctx 0 62)))
               ]))
      ]
    | Str -> [ (fun () -> none (string_literal ctx)) ]
    | Float | Arrow _ | Num _ | U _ | UTuple _ | Or_null _ | Arr _ -> []
    | List t ->
      [ (fun () -> none "[]")
      ; (fun () ->
          let ph, bh = sub t in
          let pt, bt = sub ty in
          [%string "(%{ph} :: %{pt})"], bh @ bt)
      ; (fun () ->
          let a, ba = sub t in
          let b, bb = sub t in
          [%string "[%{a}; %{b}]"], ba @ bb)
      ]
    | Option t ->
      [ (fun () -> none "None")
      ; (fun () ->
          let a, ba = sub t in
          [%string "(Some %{a})"], ba)
      ]
    | Pair (a, b) ->
      [ (fun () ->
          let pa, ba = sub a in
          let pb, bb = sub b in
          [%string "(%{pa}, %{pb})"], ba @ bb)
      ]
    | Named i ->
      (match ctx.decls.(i) with
       | Record fields ->
         [ (fun () ->
             let picked =
               match List.filter (fun _ -> flip ctx) fields with
               | [] -> [ List.hd fields ]
               | picked -> picked
             in
             let parts =
               List.map (fun (field, field_ty, _) -> field, sub field_ty) picked
             in
             ( p
                 "{ %s_ }"
                 (String.concat
                    ""
                    (List.map
                       (fun (field, (pat, _)) -> [%string "%{field} = %{pat}; "])
                       parts))
             , List.concat_map (fun (_, (_, binds)) -> binds) parts ))
         ]
       | Variant constrs ->
         List.map
           (fun (c, args) () ->
              let parts = List.map sub args in
              construct c (List.map fst parts), List.concat_map snd parts)
           constrs
       | URecord _ -> [])
  in
  let combined =
    if structural = []
    then []
    else
      [ (fun () ->
          let a, _ = pattern ctx ty (depth - 1) ~binds:false in
          let b, _ = pattern ctx ty (depth - 1) ~binds:false in
          none [%string "(%{a} | %{b})"])
      ]
      @
      if binds
      then
        [ (fun () ->
            let q, bq = sub ty in
            let x = fresh ctx "q" in
            [%string "(%{q} as %{x})"], (x, ty) :: bq)
        ]
      else []
  in
  if depth <= 0
  then choose ctx [ (fun () -> none "_"); var ]
  else if structural <> [] && (top || flip ~p:0.75 ctx)
  then choose ctx (structural @ combined)
  else choose ctx [ (fun () -> none "_"); var ]
;;
