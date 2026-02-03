[@@@ocaml.warning "-26"]
[@@@ocaml.warning "-32"]

open Smt
open Smt.Symbol

let bad_input = "(((((((((((a - 1) - 1) - 1) - 1) - 1) - 1) - 1) - 1) - 1) - 1) <= 0) ^ (not ((((((((((a - 1) - 1) - 1) - 1) - 1) - 1) - 1) - 1) - 1) <= 0)) ^ (not (((((((((a - 1) - 1) - 1) - 1) - 1) - 1) - 1) - 1) <= 0)) ^ ((((((((a - 1) - 1) - 1) - 1) - 1) - 1) - 1) <= 0) ^ (not (((((((a - 1) - 1) - 1) - 1) - 1) - 1) <= 0)) ^ ((((((a - 1) - 1) - 1) - 1) - 1) <= 0) ^ (not (((((a - 1) - 1) - 1) - 1) <= 0)) ^ ((((a - 1) - 1) - 1) <= 0) ^ (not (((a - 1) - 1) <= 0)) ^ (not ((a - 1) <= 0)) ^ (not (a <= 0))"

let ast = Boolean.parse bad_input

module Bluesclues = Formula.Make_solver (Overlays.Typed_z3)

let result = Bluesclues.solve [ast];;

let () =
  match result with
  | Solution.Sat result -> 
    let result_text = Model.to_string result [AsciiSymbol.make_int 'a'] ~pp_assignment:(fun (I k) v -> (
      "%s => %s" (Int.to_string k) (Int.to_string v)
    )) in
    Printf.printf "%s\n", result_text;
  | _ -> Printf.printf "unknown or unsat\n";
