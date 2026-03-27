[@@@ocaml.warning "-26"]
[@@@ocaml.warning "-27"]
[@@@ocaml.warning "-32"]

open Printf
open Smt
open Smt.Symbol
open Overlays

module B3 = Formula.Make_solver (Blue3)

let formula = Boolean.parse "(a < 65) ^ (a < 48) ^ (not (a = 108)) ^ (not (a = 105)) ^ (not (a = 98)) ^ (not (a = 97)) ^ (not (a = 61)) ^ (not (a = 45)) ^ (not (a = 43)) ^ (not (a = 42)) ^ (not (a = 41)) ^ (not (a = 40)) ^ (not (a = 32)) ^ (97 <= a)"
let rewritten = Formula.rewrite formula

let pp_solution = Solution.to_string 
  ~pp_assignment:(fun (I x) v -> sprintf "%c => %d" (Char.chr x) v)
  ~symbol:(fun uid -> Char.chr uid |> AsciiSymbol.make_int)

let () =
  printf "%s\n" (Formula.to_string rewritten);
