open Ty

let rec printer = function
  | Int -> "string_of_int"
  | Bool -> "string_of_bool"
  | Float -> "show_float"
  | Char -> "Char.escaped"
  | Int64 -> "Int64.to_string"
  | Str -> {|(Printf.sprintf "%S")|}
  | List t ->
    [%string {|(fun l -> "[" ^ String.concat "; " (List.map %{printer t} l) ^ "]")|}]
  | Option t ->
    [%string {|(function None -> "None" | Some v -> "Some (" ^ %{printer t} v ^ ")")|}]
  | Pair (a, b) ->
    [%string {|(fun (a, b) -> "(" ^ %{printer a} a ^ ", " ^ %{printer b} b ^ ")")|}]
  | Arrow _ -> {|(fun _ -> "<fun>")|}
  | Arr t when not (restricted t) ->
    [%string
      {|(fun a -> "[|" ^ String.concat "; " (Array.to_list (Array.map %{printer t} a)) ^ "|]")|}]
  | Arr t ->
    [%string
      {|(fun a -> "[|" ^ String.concat "; " (List.init (array_length a) (fun i -> %{printer t} (array_get a i))) ^ "|]")|}]
  | UTuple ts ->
    let xs = List.mapi (fun i _ -> "x" ^ string_of_int i) ts in
    let shown =
      String.concat
        {| ^ ", " ^ |}
        (List.map2 (fun x t -> [%string "%{printer t} %{x}"]) xs ts)
    in
    let pattern = Config.ox_syntax "#" "" ^ "(" ^ String.concat ", " xs ^ ")" in
    [%string {|(fun %{pattern} -> "#(" ^ %{shown} ^ ")")|}]
  | Named i -> [%string "show_t%{i#Int}"]
  | t when is_num t ->
    if is_float t
    then [%string {|(fun (x : %{t#Ty}) -> show_float %{convert t Float "x"})|}]
    else [%string {|(fun (x : %{t#Ty}) -> Int64.to_string %{convert t Int64 "x"})|}]
  | _ -> {|(fun _ -> "<unprintable>")|}
;;

let declaration ?parent i decl =
  match decl with
  | Record fields ->
    let field_decl { name; ty; is_mutable } =
      [%string {|%{if is_mutable then "mutable " else ""}%{name} : %{ty#Ty}|}]
    in
    let show { name; ty; _ } = [%string {|"%{name} = " ^ %{printer ty} v.%{name}|}] in
    (* OxCaml requires a layout attribute on records of only boxed and unboxed
       floats. *)
    let has ty = List.exists (fun field -> field.ty = ty) fields in
    let flatten =
      if
        List.for_all (fun field -> field.ty = Float || field.ty = unboxed_float) fields
        && has Float
        && has unboxed_float
      then Config.ox_syntax " [@@flatten_floats]" ""
      else ""
    in
    let decls = String.concat "; " (List.map field_decl fields) in
    let shows = String.concat {| ^ "; " ^ |} (List.map show fields) in
    [%string "type t%{i#Int} = { %{decls} }%{flatten}\n"]
    ^ [%string {|let show_t%{i#Int} (v : t%{i#Int}) = "{" ^ %{shows} ^ "}"|}]
    ^ "\n"
  | URecord fields ->
    let field_decl (field, field_ty) = [%string "%{field} : %{field_ty#Ty}"] in
    let decls = String.concat "; " (List.map field_decl fields) in
    let hash = Config.ox_syntax "#" "" in
    [%string "type t%{i#Int} = %{hash}{ %{decls} }\n"]
  | Variant constrs ->
    let constr (c, args) =
      match args with
      | [] -> c
      | _ when List.mem c !Config.inline_records ->
        let fields = List.mapi (fun i t -> [%string "r%{i#Int} : %{t#Ty}"]) args in
        [%string {|%{c} of { %{String.concat "; " fields} }|}]
      | _ -> [%string {|%{c} of %{String.concat " * " (List.map show_ty args)}|}]
    in
    let show (c, args) =
      match args with
      | [] -> [%string {|%{c} -> "%{c}"|}]
      | _ ->
        let xs = List.mapi (fun j _ -> [%string "a%{j#Int}"]) args in
        let shown =
          String.concat
            {| ^ ", " ^ |}
            (List.map2 (fun x t -> [%string "%{printer t} %{x}"]) xs args)
        in
        [%string {|%{Literal.construct c xs} -> "%{c} (" ^ %{shown} ^ ")"|}]
    in
    let alts cs = String.concat " | " (List.map constr cs) in
    let body =
      match parent with
      | Some (j, inherited) ->
        let own = List.filter (fun c -> not (List.mem c inherited)) constrs in
        [%string "[ t%{j#Int} | %{alts own} ]"]
      | None when (fst (List.hd constrs)).[0] = '`' -> [%string "[ %{alts constrs} ]"]
      | None -> alts constrs
    in
    let shows = String.concat " | " (List.map show constrs) in
    [%string
      "type t%{i#Int} = %{body}\n\
       let show_t%{i#Int} (v : t%{i#Int}) = match v with %{shows}\n"]
;;
