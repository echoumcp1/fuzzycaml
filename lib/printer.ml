open Ty

let p = Printf.sprintf

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
    let field (f, t, m) = [%string {|%{if m then "mutable " else ""}%{f} : %{t#Ty}|}] in
    let show (f, t, _) = [%string {|"%{f} = " ^ %{printer t} v.%{f}|}] in
    (* OxCaml requires a layout attribute on records of only boxed and unboxed
       floats. *)
    let has t = List.exists (fun (_, t', _) -> t' = t) fields in
    let flatten =
      if
        List.for_all (fun (_, t, _) -> t = Float || t = float_u) fields
        && has Float
        && has float_u
      then " [@@flatten_floats]"
      else ""
    in
    p
      "type t%d = { %s }%s\nlet show_t%d (v : t%d) = \"{\" ^ %s ^ \"}\"\n"
      i
      (String.concat "; " (List.map field fields))
      flatten
      i
      i
      (String.concat {| ^ "; " ^ |} (List.map show fields))
  | URecord fields ->
    p
      "type t%d = #{ %s }\n"
      i
      (String.concat "; " (List.map (fun (f, t) -> [%string "%{f} : %{t#Ty}"]) fields))
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
        p
          {|%s (%s) -> "%s (" ^ %s ^ ")"|}
          c
          (String.concat ", " xs)
          c
          (String.concat
             {| ^ ", " ^ |}
             (List.map2 (fun x t -> [%string "%{printer t} %{x}"]) xs args))
    in
    let alts cs = String.concat " | " (List.map constr cs) in
    let body =
      match parent with
      | Some (j, inherited) ->
        [%string
          "[ t%{j#Int} | %{alts (List.filter (fun c -> not (List.mem c inherited)) \
           constrs)} ]"]
      | None when (fst (List.hd constrs)).[0] = '`' -> [%string "[ %{alts constrs} ]"]
      | None -> alts constrs
    in
    p
      "type t%d = %s\nlet show_t%d (v : t%d) = match v with %s\n"
      i
      body
      i
      i
      (String.concat " | " (List.map show constrs))
;;
