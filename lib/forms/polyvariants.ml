open Config
open Ty
open Ctx
open Gen_ty
open Env

(* Matches on polymorphic variants test hashes of the tags, so these hash to
   values spread over the whole range, negative ones included. No two collide,
   which the type checker would reject. *)
let tag_names =
  [ "A"
  ; "B"
  ; "C"
  ; "Z"
  ; "Go"
  ; "X1"
  ; "Yy"
  ; "Bar"
  ; "End"
  ; "Foo"
  ; "Int"
  ; "Nil"
  ; "Red"
  ; "Empty"
  ; "Blue"
  ; "Cons"
  ; "Green"
  ; "Leaf"
  ; "Node"
  ; "Pair"
  ; "Some_value"
  ; "Orange"
  ; "Cherry"
  ; "Peach"
  ; "Branch"
  ; "Zzzzzzzz"
  ]
;;

type tag =
  { name : string
  ; args : ty list
  }

type annotation =
  | Exact
  | Open
  | Upper
  | Coerced of tag list

let quoted tag = "`" ^ tag.name

let show_tag tag =
  match tag.args with
  | [] -> quoted tag
  | args -> [%string "%{quoted tag} of %{String.concat \" * \" (List.map show_ty args)}"]
;;

let row tags = String.concat " | " (List.map show_tag tags)
let closed tags = [%string "[ %{row tags} ]"]
let wildcard tag = if tag.args = [] then quoted tag else [%string "%{quoted tag} _"]

let rec distinct ctx count available =
  if count = 0
  then []
  else (
    let name = pick ctx available in
    name :: distinct ctx (count - 1) (List.filter (( <> ) name) available))
;;

(* Variants without arguments are immediates, so their matches switch on the
   hashes alone, which mixed variants with many tags rarely reach. *)
let draw_tags ctx =
  let constant = flip ~p:0.3 ctx in
  let names = distinct ctx (int_in ctx 2 12) tag_names in
  List.map
    (fun name ->
       { name
       ; args = (if constant then [] else repeat ctx 0 2 (fun _ -> value_type ctx))
       })
    names
;;

let construct env gen tag =
  match tag.args with
  | [] -> quoted tag
  | args ->
    [%string "(%{quoted tag} (%{String.concat \", \" (List.map (gen.expr env) args)}))"]
;;

(* With an opaque index, the compiler cannot know which tag the value has. *)
let build ctx env gen tags =
  choose
    ctx
    [ (fun () -> construct env gen (pick ctx tags))
    ; (fun () ->
        let condition = gen.expr env Bool in
        let first = construct env gen (pick ctx tags) in
        let second = construct env gen (pick ctx tags) in
        [%string "(if %{condition} then %{first} else %{second})"])
    ; (fun () ->
        let index = gen.expr env Int in
        let count = List.length tags in
        let arms =
          List.mapi
            (fun i tag ->
               let pattern = if i = count - 1 then "_" else string_of_int i in
               [%string "| %{pattern} -> %{construct env gen tag}"])
            tags
        in
        [%string
          "(match (Sys.opaque_identity %{index} land max_int) mod %{count#Int} with \
           %{String.concat \" \" arms})"])
    ]
;;

let arg_patterns ctx tag ~binds =
  let parts = List.map (fun arg_ty -> Pattern.pattern ctx arg_ty 2 ~binds) tag.args in
  let pattern =
    match parts with
    | [] -> quoted tag
    | parts -> [%string "(%{quoted tag} (%{String.concat \", \" (List.map fst parts)}))"]
  in
  pattern, List.concat_map snd parts
;;

let refined ctx env ty gen var tags =
  let arm tag =
    let vars = List.map (fun arg_ty -> fresh ctx "q", arg_ty) tag.args in
    let pattern =
      match vars with
      | [] -> quoted tag
      | vars -> [%string "(%{quoted tag} (%{String.concat \", \" (List.map fst vars)}))"]
    in
    [%string "| %{pattern} -> %{gen.expr (bind_all env vars) ty}"]
  in
  [%string "(match %{var} with %{String.concat \" \" (List.map arm tags)})"]
;;

let polyvariant ctx env ty gen =
  let tags = draw_tags ctx in
  let annotation =
    choose
      ctx
      [ (fun () -> Exact)
      ; (fun () -> Open)
      ; (fun () -> Upper)
      ; (fun () ->
          match subset ctx 12 tags with
          | [] -> Coerced [ List.hd tags ]
          | smaller -> Coerced smaller)
      ]
  in
  let value =
    match annotation with
    | Exact -> [%string "(%{build ctx env gen tags} : %{closed tags})"]
    | Open -> [%string "(%{build ctx env gen tags} : [> %{row tags} ])"]
    | Upper -> [%string "(%{build ctx env gen tags} : [< %{row tags} ])"]
    | Coerced smaller ->
      let built = build ctx env gen smaller in
      [%string "(%{built} : %{closed smaller} :> %{closed tags})"]
  in
  let scrutinee = fresh ctx "pv" in
  let local_types = ref [] in
  let nonempty_subset () =
    match subset ctx 12 tags with
    | [] -> [ List.hd tags ]
    | some -> some
  in
  let arm () =
    choose
      ctx
      ([ (fun () ->
           let pattern, bound = arg_patterns ctx (pick ctx tags) ~binds:true in
           let arm_env = bind_all env bound in
           let guard =
             if flip ~p:0.3 ctx then [%string " when %{gen.expr arm_env Bool}"] else ""
           in
           [%string "| %{pattern}%{guard} -> %{gen.expr arm_env ty}"])
       ; (fun () ->
           let alternatives = nonempty_subset () in
           let patterns =
             List.map (fun tag -> fst (arg_patterns ctx tag ~binds:false)) alternatives
           in
           let pattern = [%string "(%{String.concat \" | \" patterns})"] in
           if flip ctx
           then (
             let var = fresh ctx "w" in
             [%string
               "| (%{pattern} as %{var}) -> %{refined ctx env ty gen var alternatives}"])
           else [%string "| %{pattern} -> %{gen.expr env ty}"])
       ; (fun () ->
           let alternatives = nonempty_subset () in
           let module_name = fresh ctx "Pv" in
           local_types := (module_name, alternatives) :: !local_types;
           let var = fresh ctx "w" in
           [%string
             "| (#%{module_name}.t as %{var}) -> %{refined ctx env ty gen var \
              alternatives}"])
       ]
       @
       match annotation with
       | Open ->
         [ (fun () ->
             let other =
               pick
                 ctx
                 (List.filter
                    (fun name -> not (List.exists (fun tag -> tag.name = name) tags))
                    tag_names)
             in
             [%string "| `%{other} -> %{gen.expr env ty}"])
         ]
       | Exact | Upper | Coerced _ -> [])
  in
  let arms = List.init (int_in ctx 1 5) (fun _ -> arm ()) in
  let last =
    if flip ctx
    then [%string "| _ -> %{gen.expr env ty}"]
    else (
      let every = String.concat " | " (List.map wildcard tags) in
      [%string "| %{every} -> %{gen.expr env ty}"])
  in
  let modules =
    String.concat
      ""
      (List.rev_map
         (fun (module_name, alternatives) ->
            [%string
              "let module %{module_name} = struct type t = %{closed alternatives} end in "])
         !local_types)
  in
  let matched =
    if flip ctx then [%string "(Sys.opaque_identity %{scrutinee})"] else scrutinee
  in
  [%string
    "(let %{scrutinee} = %{value} in %{modules}match %{matched} with %{String.concat \" \
     \" arms} %{last})"]
;;

let forms ctx env ty gen =
  boost (if on "polyvariants" then [ (fun () -> polyvariant ctx env ty gen) ] else [])
;;
