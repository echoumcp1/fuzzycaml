open Config
open Ty
open Ctx

let rec gen_ty ?(unboxed = false) ctx ~first_order depth =
  let sub () = gen_ty ctx ~first_order (depth - 1) in
  let named =
    List.filter
      (fun i -> ((not first_order) || not !mixed.(i)) && (unboxed || not !urec.(i)))
      (List.init (Array.length ctx.decls) Fun.id)
  in
  let ox f = !ox_mode && on f in
  let nums =
    List.map (fun n -> Num n) (if first_order then [ I8; I16; I32; Nat ] else all_nb)
  in
  choose
    ctx
    ([ (fun () -> Int)
     ; (fun () -> Bool)
     ; (fun () -> Float)
     ; (fun () -> Float)
     ; (fun () -> Float)
     ; (fun () -> Char)
     ; (fun () -> Int64)
     ]
     @ (if on "strings" then [ (fun () -> Str) ] else [])
     @ (if named <> [] then [ (fun () -> Named (pick ctx named)) ] else [])
     @ (if unboxed && !ox_mode then [ (fun () -> float_u) ] else [])
     @ (if ox "numbers" then List.map (fun t () -> t) nums else [])
     @ (if unboxed && ox "numbers" then List.map (fun u () -> U u) all_ub else [])
     @ (if unboxed && depth > 0 && ox "utuples"
        then
          [ (fun () ->
              UTuple
                (List.init (int_in ctx 2 3) (fun _ ->
                   gen_ty ~unboxed:true ctx ~first_order (depth - 1))))
          ]
        else [])
     @ (if unboxed && depth > 0 && ox "or_null"
        then [ (fun () -> Or_null (sub ())) ]
        else [])
     @ (if (not first_order) && depth > 0 && on "arrays"
        then [ (fun () -> Arr (array_elem ctx (depth - 1))) ]
        else [])
     @ (if depth = 0
        then []
        else
          [ (fun () -> List (sub ()))
          ; (fun () -> Option (sub ()))
          ; (fun () ->
              let a = sub () in
              Pair (a, sub ()))
          ])
     @
     if depth = 0 || first_order
     then []
     else
       [ (fun () ->
           let a = gen_ty ~unboxed:true ctx ~first_order (depth - 1) in
           Arrow (a, gen_ty ~unboxed:true ctx ~first_order (depth - 1)))
       ])

(* Floats are more likely, since float arrays are stored flat. *)
and array_elem ctx depth =
  choose
    ctx
    ([ (fun () -> Int); (fun () -> Float); (fun () -> Int64) ]
     @ (if not !ox_mode
        then [ (fun () -> Float); (fun () -> gen_ty ctx ~first_order:false depth) ]
        else if on "numbers"
        then List.map (fun t () -> t) newer_nums
        else [ (fun () -> float_u) ])
     @ if depth > 0 then [ (fun () -> Arr (array_elem ctx (depth - 1))) ] else [])
;;

let any_ty ctx = gen_ty ctx ~first_order:false 2
let top_ty ctx = gen_ty ~unboxed:true ctx ~first_order:false 2
let fo_ty ctx = gen_ty ctx ~first_order:true 2
