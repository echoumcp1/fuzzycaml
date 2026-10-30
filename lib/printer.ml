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
  | Arr t
    when match t with
         | U _ -> false
         | _ -> true ->
    [%string
      {|(fun a -> "[|" ^ String.concat "; " (Array.to_list (Array.map %{printer t} a)) ^ "|]")|}]
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
    let field_decl (field, field_ty, is_mutable) =
      [%string {|%{if is_mutable then "mutable " else ""}%{field} : %{field_ty#Ty}|}]
    in
    let show (field, field_ty, _) =
      [%string {|"%{field} = " ^ %{printer field_ty} v.%{field}|}]
    in
    (* OxCaml requires a layout attribute on records of only boxed and unboxed
       floats. *)
    let has t = List.exists (fun (_, field_ty, _) -> field_ty = t) fields in
    let flatten =
      if
        List.for_all
          (fun (_, field_ty, _) -> field_ty = Float || field_ty = float_u)
          fields
        && has Float
        && has float_u
      then " [@@flatten_floats]"
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
    [%string "type t%{i#Int} = #{ %{decls} }\n"]
  | Variant constrs ->
    let constr (c, args) =
      match args with
      | [] -> c
      | _ -> [%string {|%{c} of %{String.concat " * " (List.map show_ty args)}|}]
    in
    let show (c, args) =
      match args with
      | [] -> [%string {|%{c} -> "%{c}"|}]
      | _ ->
        let xs = List.mapi (fun j _ -> [%string "a%{j#Int}"]) args in
        let vars = String.concat ", " xs in
        let shown =
          String.concat
            {| ^ ", " ^ |}
            (List.map2 (fun x t -> [%string "%{printer t} %{x}"]) xs args)
        in
        [%string {|%{c} (%{vars}) -> "%{c} (" ^ %{shown} ^ ")"|}]
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
