[@@@ocaml.warning "-26"]
[@@@ocaml.warning "-27"]
[@@@ocaml.warning "-32"]

open Smt
open Smt.Symbol

let x1 = AsciiSymbol.make_int 'a'
let x2 = AsciiSymbol.make_int 'b'
let x3 = AsciiSymbol.make_int 'c'
let x4 = AsciiSymbol.make_int 'd'

module Solver = Smt.Formula.Make_solver (struct
  include Overlays.Typed_z3
  let splits = [Splits.neq]
  let logics : (module Formula.LOGIC) list = [(module Diff)]
end)

open Core
let () =
  let formula = Formula.And [
    Binop (Binop.Less_than, Key x1, Const_int 0)
  ]
  in
  let extracted = Diff.extract formula in
  List.iter extracted ~f:(fun {x; y; c;} -> (
    printf "x%d <= x%d%s" x y (if c < 0 then " - " ^ Int.to_string (-c) else " + " ^ Int.to_string c)
  ));
  let result = Solver.solve [formula] in
  match result with
  | Solution.Sat model -> printf "ok\n"
  | Solution.Unsat -> printf "uh oh\n"
  | Solution.Unknown -> failwith "lol"
