let rec convert_to_sat (r: unit Dfa.re) =
    match r.re with
    | R_empty -> ""
    | R_end _ -> ""
    | R_chars (char_set, _) ->
        let items:string = (Dfa.CharSet.fold
        (fun c acc -> acc ^ (String.make 1 c)) char_set "") in
            items
    | R_choice (a, b) ->
            (* sigma rule *)
        (match ((convert_to_sat a), (convert_to_sat b)) with
            | ("", "") -> ""
            | ("", b) -> b
            | (a, "") -> a
            | (x, y) -> "(re.union " ^ x ^ " " ^ y ^ ")")
    | R_seq (r0, r1) ->
        (match ((convert_to_sat r0), (convert_to_sat r1)) with
            | ("", "") -> ""
            | ("", b) -> b
            | (a, "") -> a
            | (a, b) -> "(re.++ " ^ a ^ " " ^ b ^ ")")
    | R_star r -> "(re.* " ^ (convert_to_sat r) ^ " )";;
