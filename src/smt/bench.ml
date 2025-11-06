open Core
open Smt.Formula
open Smt.Symbol
open Formula_2.Solveable

module Symbol = Make(struct 
    type t = string
    let uid s = Hashtbl.hash s
end)

let () =
    let a = Key (Symbol.make_int "a") and b = Key (Symbol.make_int "b")
    in
    let exprs = [
        ("true", [ Const_bool true ]);
        ("false", [ Const_bool false ]);
        ("not true", [ Not (Const_bool true) ]);
        ("not false", [ Not (Const_bool false) ]);
        ("a = a", [ Binop (Equal, a, a) ]);
        ("not (a = a)", [ Not (Binop (Equal, a, a)) ]);
        ("a = 1", [ Binop (Equal, a, Const_int 1) ]);
        ("a = 1 ^ a != 1", [ And [ Binop (Equal, a, Const_int 1); Not (Binop (Equal, a, Const_int 1)) ] ]);
        ("a = 1 ^ b = 1", [ And [ Binop (Equal, a, Const_int 1); Binop (Equal, b, Const_int 1) ] ]);
        ("a = 1 ^ b = 1 ^ a != b", [ And [
            Binop (Equal, a, Const_int 123456);
            Binop (Equal, b, Const_int 123456);
            Not (Binop (Equal, a, b))
        ] ])
    ] 
    in
    List.iter exprs ~f:(fun (label, expr_list) ->
        let start_ns = Time_ns.now () in
        let result = solve expr_list in
        let elapsed_ns =
            Time_ns.diff (Time_ns.now ()) start_ns
            |> Time_ns.Span.to_int_ns
        in
        Printf.printf
            "=== %s ===\nResult: %s\nTime: %d ns\n\n"
            label
            (Smt.Solution.to_string result)
            elapsed_ns
    )

