open Core
open Smt.Formula
open Smt.Symbol
open Formula_2

module Symbol = Make(struct 
    type t = string
    let uid (s : string) =
        String.fold s ~init:0 ~f:(fun acc c -> acc + Char.to_int c)
end)

let () =
    (* let cnf : string cnf = [ *)
    (*     [Pos "A"]; *)
    (*     [Neg "A"]; *)
    (* ] in *)
    (*   match dpll String.equal [] cnf with *)
    (* | None -> print_endline "UNSAT"; *)
    (* | Some assignment -> *)
    (*     List.iter assignment ~f:(fun (v, b) -> *)
    (*         printf "  %s = %b\n" v b); *)
    let a = Key (Symbol.make_int "a")
    in
    let exprs = [
        (* ("true", [ Const_bool true ]); *)
        (* ("false", [ Const_bool false ]); *)
        (* ("not true", [ Not (Const_bool true) ]); *)
        (* ("not false", [ Not (Const_bool false) ]); *)
        (* ("a = a", [ Binop (Equal, a, a) ]); *)
        (* ("not (a = a)", [ Not (Binop (Equal, a, a)) ]); *)
        (* ("a = 1", [ Binop (Equal, a, Const_int 1) ]); *)
        (* ("a = 1 ^ a != 1", [ And [ Binop (Equal, a, Const_int 1); Not (Binop (Equal, a, Const_int 1)) ] ]); *)
        (* ("a = 1 ^ b = 1", [ And [ Binop (Equal, a, Const_int 1); Binop (Equal, b, Const_int 1) ] ]); *)
        ("a > 3 ^ a < 5", [
            And [
                Binop (Greater_than, a, Const_int 3);
                Binop (Less_than, a, Const_int 5);
            ]
        ]);
        ("a > 3 ^ a < 2", [
            And [
                Binop (Greater_than, a, Const_int 3);
                Binop (Less_than, a, Const_int 2);
            ]
        ])
    ] 
    in
    List.iter exprs ~f:(fun (label, expr_list) ->
        let start_ns = Time_ns.now () in
        let result = solve expr_list in
        let elapsed_ns =
            Time_ns.diff (Time_ns.now ()) start_ns
            |> Time_ns.Span.to_int_ns
        in
        Printf.printf "=== %s ===\nResult: %s\nTime: %d ns\n\n" label (Smt.Solution.to_string result) elapsed_ns
    );
