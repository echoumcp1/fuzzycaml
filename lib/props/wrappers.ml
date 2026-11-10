open Config
open Ty
open Ctx
open Gen_ty
open Literal
open Env

let junk env ty gen = without_checks (fun () -> gen.expr (pure env) ty)
let any_junk env shape gen = without_checks (fun () -> gen.of_shape (pure env) shape)
let value ty = not (restricted ty)

let float_width = function
  | Num F32 | Unboxed UFloat32 -> 32
  | _ -> 64
;;

(* Whether every [a] converts to [b] and back unchanged. *)
let lossless from_ty to_ty =
  from_ty <> to_ty
  && is_num from_ty
  && is_num to_ty
  && is_float from_ty = is_float to_ty
  &&
  if is_float from_ty
  then float_width to_ty >= float_width from_ty
  else width to_ty >= width from_ty && (width from_ty < 64 || width to_ty = 64)
;;

let numbers = [ Int; Int64; Float ] @ newer_numbers

type field_slot =
  { record_decl : int
  ; field : string
  ; fields : (string * ty) list
  ; unboxed : bool
  }

type arg_slot =
  { variant_decl : int
  ; constructor : string
  ; args : ty list
  ; position : int
  }

(* A container of [ty], built from [x] and taken apart again. The container is
   passed directly, through a let, or through a function the compiler does not
   inline. *)
let carry ctx container_ty inject project wrapped =
  let container_var = fresh ctx "s" in
  let container_name = show_ty container_ty in
  choose
    ctx
    ([ (fun () -> project (inject wrapped))
     ; (fun () ->
         [%string
           "(let %{container_var} : %{container_name} = %{inject wrapped} in %{project \
            container_var})"])
     ; (fun () ->
         let fn = fresh ctx "out" in
         [%string
           "(let[@inline never] %{fn} (%{container_var} : %{container_name}) = %{project \
            container_var} in %{fn} %{inject wrapped})"])
     ]
     @ gate
         (value container_ty)
         [ (fun () -> project [%string "(Sys.opaque_identity %{inject wrapped})"]) ])
;;

(* An expression context that returns the value of type [ty] put in it. *)
let rec layer ctx env ty gen x =
  let ty_name = show_ty ty in
  let var = fresh ctx "v" in
  let up_to count = int_in ctx 0 count in
  let more_junk shape =
    List.init (int_in ctx 0 2) (fun _ -> snd (any_junk env shape gen))
  in
  let fields_of_ty =
    List.concat_map
      (fun (decl, decl_def) ->
         match decl_def with
         | Record fields ->
           List.filter_map
             (fun (field : record_field) ->
                if field.ty = ty
                then
                  Some
                    { record_decl = decl
                    ; field = field.name
                    ; fields = field_types fields
                    ; unboxed = false
                    }
                else None)
             fields
         | URecord fields ->
           List.filter_map
             (fun (name, field_ty) ->
                if field_ty = ty
                then Some { record_decl = decl; field = name; fields; unboxed = true }
                else None)
             fields
         | Variant _ -> [])
      (indexed_decls ctx)
  in
  let args_of_ty =
    List.concat_map
      (fun (decl, decl_def) ->
         match decl_def with
         | Variant constrs ->
           List.concat_map
             (fun (constructor, args) ->
                List.concat
                  (List.mapi
                     (fun position arg_ty ->
                        if arg_ty = ty
                        then [ { variant_decl = decl; constructor; args; position } ]
                        else [])
                     args))
             constrs
         | Record _ | URecord _ -> [])
      (indexed_decls ctx)
  in
  let wider_types = List.filter (lossless ty) numbers in
  let closable = env.mutables = [] && env.locals = [] in
  choose
    ctx
    ([ (fun () ->
         let before = more_junk (Any all_types) in
         let after =
           snd (any_junk env (Any all_types) gen) :: more_junk (Any all_types)
         in
         let count = List.length before in
         let pattern =
           String.concat
             ", "
             (List.init count (fun _ -> "_") @ [ var ] @ List.map (fun _ -> "_") after)
         in
         [%string
           "(let #(%{pattern}) = #(%{String.concat \", \" (before @ [ x ] @ after)}) in \
            %{var})"])
     ; (fun () ->
         let fn = fresh ctx "id" in
         [%string
           "(let[@inline never] %{fn} (%{var} : %{ty_name}) = %{var} in %{fn} %{x})"])
     ; (fun () ->
         let junk_expr =
           without_checks (fun () -> gen.expr { env with locals = [] } ty)
         in
         [%string "(if Sys.opaque_identity false then %{junk_expr} else %{x})"])
     ; (fun () -> layer ctx env ty gen (layer ctx env ty gen x))
     ]
     @ gate
         (value ty)
         [ (fun () ->
             let junk_ty, junk_expr = any_junk env (Any value_types) gen in
             let on_left = flip ctx in
             carry
               ctx
               (if on_left then Pair (ty, junk_ty) else Pair (junk_ty, ty))
               (fun x ->
                  if on_left
                  then [%string "(%{x}, %{junk_expr})"]
                  else [%string "(%{junk_expr}, %{x})"])
               (fun container ->
                  choose
                    ctx
                    [ (fun () ->
                        [%string "(%{if on_left then \"fst\" else \"snd\"} %{container})"])
                    ; (fun () ->
                        let destructure =
                          if on_left
                          then [%string "(%{var}, _)"]
                          else [%string "(_, %{var})"]
                        in
                        [%string "(let %{destructure} = %{container} in %{var})"])
                    ])
               x)
         ; (fun () ->
             carry
               ctx
               (Option ty)
               (fun x -> [%string "(Some %{x})"])
               (fun container ->
                  [%string
                    "(match %{container} with Some %{var} -> %{var} | None -> %{junk env \
                     ty gen})"])
               x)
         ; (fun () ->
             let before = List.init (up_to 2) (fun _ -> junk env ty gen) in
             let after = List.init (up_to 2) (fun _ -> junk env ty gen) in
             let position = List.length before in
             carry
               ctx
               (List ty)
               (fun x -> [%string "[%{String.concat \"; \" (before @ [ x ] @ after)}]"])
               (fun container ->
                  choose
                    ctx
                    [ (fun () -> [%string "(List.nth %{container} %{position#Int})"])
                    ; (fun () ->
                        let destructure =
                          String.concat
                            " :: "
                            (List.init position (fun _ -> "_") @ [ var; "_" ])
                        in
                        [%string
                          "(match %{container} with %{destructure} -> %{var} | _ -> \
                           %{junk env ty gen})"])
                    ])
               x)
         ; (fun () ->
             [%string "(let %{var} = ref %{junk env ty gen} in %{var} := %{x}; !%{var})"])
         ; (fun () -> [%string "(Sys.opaque_identity %{x})"])
         ; (fun () ->
             let exn = fresh ctx "E" in
             [%string
               "(let exception %{exn} of %{ty_name} in try raise (%{exn} %{x}) with \
                %{exn} %{var} -> %{var})"])
         ]
     (* A closure cannot use a [let mutable] or a local in scope. *)
     @ gate
         closable
         [ (fun () ->
             let junk_ty, junk_expr = any_junk env (Any all_types) gen in
             carry
               ctx
               (Arrow (junk_ty, ty))
               (fun x -> [%string "(fun (_ : %{junk_ty#Ty}) -> %{x})"])
               (fun container -> [%string "(%{container} %{junk_expr})"])
               x)
         ]
     @ gate
         (value ty && closable)
         [ (fun () -> [%string "(Lazy.force (lazy %{x}))"])
         ; (fun () ->
             let module_ = fresh ctx "M" in
             [%string
               "(let module %{module_} = struct type _ Effect.t += Ask : %{ty_name} \
                Effect.t end in Effect.Deep.match_with (fun () -> Effect.perform \
                %{module_}.Ask) () { Effect.Deep.retc = (fun %{var} -> %{var}); exnc = \
                raise; effc = (fun (type a) (e : a Effect.t) -> match e with \
                %{module_}.Ask -> Some (fun (k : (a, _) Effect.Deep.continuation) -> \
                Effect.Deep.continue k %{x}) | _ -> None) })"])
         ]
     (* Arrays of unboxed products are restricted. *)
     @ gate
         (value ty
          ||
          match ty with
          | Unboxed _ -> true
          | _ -> false)
         [ (fun () ->
             let before = List.init (up_to 2) (fun _ -> junk env ty gen) in
             let after = List.init (up_to 2) (fun _ -> junk env ty gen) in
             let at = List.length before in
             let elems = String.concat "; " (before @ [ x ] @ after) in
             [%string "(array_get [| %{elems} |] %{at#Int})"])
         ]
     @ gate
         (value ty
          &&
          match ty with
          | Or_null _ -> false
          | _ -> true)
         [ (fun () ->
             carry
               ctx
               (Or_null ty)
               (fun x -> [%string "(This %{x})"])
               (fun container ->
                  [%string
                    "(match %{container} with This %{var} -> %{var} | Null -> %{junk env \
                     ty gen})"])
               x)
         ]
     @ gate
         (immediate ty || ty = Char)
         [ (fun () ->
             let pair = fresh ctx "p" in
             let _, junk_expr = any_junk env (Any value_types) gen in
             [%string
               "(let local_ %{pair} = stack_ ((%{x} : %{ty_name}), %{junk_expr}) in let \
                (%{var}, _) = %{pair} in %{var})"])
         ]
     @ gate
         (fields_of_ty <> [])
         [ (fun () ->
             let { record_decl; field; fields; unboxed } = pick ctx fields_of_ty in
             let build_record x =
               String.concat
                 "; "
                 (List.map
                    (fun (name, field_ty) ->
                       if name = field
                       then [%string "%{name} = %{x}"]
                       else [%string "%{name} = %{junk env field_ty gen}"])
                    fields)
             in
             let hash = if unboxed then "#" else "" in
             carry
               ctx
               (Named record_decl)
               (fun x -> [%string "%{hash}{ %{build_record x} }"])
               (fun container ->
                  if unboxed
                  then [%string "%{container}.#%{field}"]
                  else
                    choose
                      ctx
                      [ (fun () -> [%string "%{container}.%{field}"])
                      ; (fun () ->
                          [%string
                            "(match %{container} with { %{field} = %{var}; _ } -> %{var})"])
                      ])
               x)
         ]
     @ gate
         (args_of_ty <> [])
         [ (fun () ->
             let { variant_decl; constructor; args; position } = pick ctx args_of_ty in
             let build_args x =
               List.mapi
                 (fun i arg_ty -> if i = position then x else junk env arg_ty gen)
                 args
             in
             let destructure =
               List.mapi (fun i _ -> if i = position then var else "_") args
             in
             carry
               ctx
               (Named variant_decl)
               (fun x -> construct constructor (build_args x))
               (fun container ->
                  [%string
                    "(match %{container} with %{construct constructor destructure} -> \
                     %{var} | _ -> %{junk env ty gen})"])
               x)
         ]
     @ gate
         (wider_types <> [])
         [ (fun () ->
             let wider_ty = pick ctx wider_types in
             convert wider_ty ty (convert ty wider_ty x))
         ])
;;

let hole = "\000"

(* [s] wrapped in code that does not change its value or the program's output. *)
let neutral ctx env ty gen s =
  let key = fresh ctx "w" in
  let dead_env = { env with locals = [] } in
  let wrap context =
    match String.split_on_char '\000' context with
    | [ before; after ] ->
      Markers.wrapper key before ^ "(" ^ s ^ ")" ^ Markers.wrapper key after
    | _ -> assert false
  in
  let saved_mutables = List.filter (fun (_, elem_ty) -> value elem_ty) env.mutables in
  let arrays =
    List.filter_map
      (function
        | original, Arr elem_ty -> Some (original, elem_ty)
        | _ -> None)
      env.vars
  in
  wrap
  @@ choose
       ctx
       ([ (fun () ->
            let junk_expr = without_checks (fun () -> gen.expr dead_env ty) in
            [%string "(if Sys.opaque_identity false then %{junk_expr} else %{hole})"])
        ; (fun () ->
            let junk_expr = without_checks (fun () -> gen.expr dead_env ty) in
            [%string
              "(match Sys.opaque_identity 0 with 0 -> %{hole} | _ -> %{junk_expr})"])
        ; (fun () ->
            let _, junk_expr =
              without_checks (fun () -> gen.of_shape dead_env (Any first_order_types))
            in
            [%string
              "(for _ = 1 to Sys.opaque_identity 0 do ignore (%{junk_expr}) done; \
               %{hole})"])
        ; (fun () ->
            let collection =
              pick
                ctx
                [ "Gc.minor ()"
                ; "Gc.full_major ()"
                ; "ignore (Gc.major_slice 0)"
                ; "Gc.compact ()"
                ]
            in
            [%string "(%{collection}; %{hole})"])
        ; (fun () ->
            let _, junk_expr = any_junk env (Any all_types) gen in
            [%string "(let _ = %{junk_expr} in %{hole})"])
        ; (fun () -> layer ctx env ty gen hole)
        ]
        @ gate
            (first_order ty)
            [ (fun () ->
                let original = fresh ctx "x"
                and round_trip = fresh ctx "y" in
                let round_trip_expr = layer ctx env ty gen original in
                [%string
                  {|(let %{original} = %{hole} in let %{round_trip} = %{round_trip_expr} in if compare %{round_trip} %{original} <> 0 then print_endline "%{Markers.failure}%{key} changed a value"; %{round_trip})|}])
            ]
        @ gate
            (saved_mutables <> [])
            [ (fun () ->
                let original, elem_ty = pick ctx saved_mutables in
                let saved = fresh ctx "saved" in
                [%string
                  "(let %{saved} = %{original} in %{original} <- %{junk env elem_ty \
                   gen}; %{original} <- %{saved}; %{hole})"])
            ]
        @ gate
            (arrays <> [])
            [ (fun () ->
                let array, elem_ty = pick ctx arrays in
                let saved = fresh ctx "saved" in
                [%string
                  "(if array_length %{array} > 0 then (let %{saved} = array_get %{array} \
                   0 in array_set %{array} 0 %{junk env elem_ty gen}; array_set %{array} \
                   0 %{saved}); %{hole})"])
            ])
;;
