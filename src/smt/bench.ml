open Formula_2

open Core

let () =
    try
        let a = AsciiSymbol.make_int "a" 
        and b = AsciiSymbol.make_int "b" and c = AsciiSymbol.make_int "c" in
        let expected_sats = [
            [Smt.Formula.And [
                Binop (Equal, Key a, Key b);
                Binop (Equal, Key b, Key c);
            ]];
            [Smt.Formula.And [
                Binop (Equal, Key a, Key b);
                Binop (Equal, Key b, Const_int 123456);
            ]];
            [Smt.Formula.And [
                Binop (Equal, Key a, Key b);
            ]]
        ] in
        List.iter expected_sats ~f:(fun expr -> ignore (solve expr));
        let expected_unsats = [
            [Smt.Formula.Const_bool false];
            [Smt.Formula.And [
                Smt.Formula.Const_bool true;
                Smt.Formula.Const_bool false;
            ]];
            [Smt.Formula.And [
                Binop (Not_equal, Key a, Key a)
            ]];
            [Smt.Formula.And [
                Binop (Equal, Key a, Key b);
                Binop (Equal, Key b, Key c);
                Binop (Not_equal, Key a, Key c)
            ]];
        ] in
        List.iter expected_unsats ~f:(fun expr -> ignore (solve expr));
        (* In_channel.read_all "formulas_dedup_2.txt" *)
        (* |> of_string *)
        (* |> List.iter ~f:(fun expr -> ignore (solve [expr])); *)
        (* let impossible_expr = Smt.Formula.And [ *)
        (*     Not (Binop (Equal, Key a, Key a)) *)
        (* ] in *)
        (* let impossible_expr2 = Smt.Formula.And [ *)
        (*     Binop (Not_equal, Key a, Key a) *)
        (* ] in *)
        (* let impossible_expr3 = Smt.Formula.And [ *)
        (*     Binop (Equal, Key a, Key b); *)
        (*     Binop (Equal, Key b, Key c); *)
        (* ] in *)
        (* ignore (solve [impossible_expr]); *)
        (* ignore (solve [impossible_expr2]); *)
        (* ignore (solve [impossible_expr3]); *)
    with
        | e ->
        eprintf "Error: %s\n" (Exn.to_string e);
        exit 1

