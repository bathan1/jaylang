open Formula_2

open Core

let () =
    try
        (* In_channel.read_all "formulas_dedup.txt" *)
        (* |> of_string *)
        (* |> fun exprs -> List.take exprs 25 *)
        (* |> List.iter ~f:(fun expr -> ignore (solve [expr])); *)
        (**)
        let a = AsciiSymbol.make_int "a"
        and b = AsciiSymbol.make_int "b"
        in
        let expr = Smt.Formula.And [
            Binop (Equal, Key a, Key b);
            Binop (Equal, Key b, Const_int 1);
        ] in
        let bad_expr = Smt.Formula.And [
            Binop (Equal, Key a, Key b);
            Not (Binop (Equal, Key a, Key b))
        ] in
        ignore (solve [expr]);
        ignore (solve [bad_expr]);
    with
        | e ->
        eprintf "Error: %s\n" (Exn.to_string e);
        exit 1

