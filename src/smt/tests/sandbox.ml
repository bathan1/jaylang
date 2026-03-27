[@@@ocaml.warning "-26"]
[@@@ocaml.warning "-27"]
[@@@ocaml.warning "-32"]

open Printf
open Smt
open Smt.Symbol
open Overlays

module B3 = Formula.Make_solver (Blue3)

let formula = Boolean.parse "(not ((a % 2) = 0))"

let pp_solution = Solution.to_string 
  ~pp_assignment:(fun (I x) v -> sprintf "%c => %d" (Char.chr x) v)
  ~symbol:(fun uid -> Char.chr uid |> AsciiSymbol.make_int)

let () =
  printf "%s\n" (
    [formula]
    |> B3.solve
    |> pp_solution
  )
