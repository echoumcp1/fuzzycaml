open Ty

let rec printer = function
  | Int -> "string_of_int"
  | Bool -> "string_of_bool"
  | Float -> "show_float"
  | Char -> "Char.escaped"
  | Int64 -> "Int64.to_string"
  | Str -> {|(Printf.sprintf "%S")|}
  | List t ->
    Printf.sprintf
      {|(fun l -> "[" ^ String.concat "; " (List.map %s l) ^ "]")|}
      (printer t)
  | Option t ->
    Printf.sprintf
      {|(function None -> "None" | Some v -> "Some (" ^ %s v ^ ")")|}
      (printer t)
  | Pair (a, b) ->
    Printf.sprintf
      {|(fun (a, b) -> "(" ^ %s a ^ ", " ^ %s b ^ ")")|}
      (printer a)
      (printer b)
  | Arrow _ -> {|(fun _ -> "<fun>")|}
  | Named i -> Printf.sprintf "show_t%d" i
  | t when is_num t ->
    if is_float t
    then Printf.sprintf "(fun (x : %s) -> show_float %s)" (show_ty t) (convert t Float "x")
    else Printf.sprintf "(fun (x : %s) -> Int64.to_string %s)" (show_ty t) (convert t Int64 "x")
  | _ -> {|(fun _ -> "<unprintable>")|}
;;


let declaration ?parent i decl =
  let p = Printf.sprintf in
  match decl with
  | Record fields ->
    let field (f, t, m) = p "%s%s : %s" (if m then "mutable " else "") f (show_ty t) in
    let show (f, t, _) = p {|"%s = " ^ %s v.%s|} f (printer t) f in
    (* OxCaml requires a record of only boxed and unboxed floats to say how it
       is laid out. *)
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
      (String.concat "; " (List.map (fun (f, t) -> p "%s : %s" f (show_ty t)) fields))
  | Variant constrs ->
    let constr (c, args) =
      match args with
      | [] -> c
      | _ -> p "%s of %s" c (String.concat " * " (List.map show_ty args))
    in
    let show (c, args) =
      match args with
      | [] -> p {|%s -> "%s"|} c c
      | _ ->
        let xs = List.mapi (fun j _ -> p "a%d" j) args in
        p
          {|%s (%s) -> "%s (" ^ %s ^ ")"|}
          c
          (String.concat ", " xs)
          c
          (String.concat
             {| ^ ", " ^ |}
             (List.map2 (fun x t -> p "%s %s" (printer t) x) xs args))
    in
    let alts cs = String.concat " | " (List.map constr cs) in
    let body =
      match parent with
      | Some (j, inherited) ->
        p "[ t%d | %s ]" j (alts (List.filter (fun c -> not (List.mem c inherited)) constrs))
      | None when (fst (List.hd constrs)).[0] = '`' -> p "[ %s ]" (alts constrs)
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
