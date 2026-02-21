[@@@ocaml.warning "-26"]
[@@@ocaml.warning "-27"]
[@@@ocaml.warning "-32"]

open Smt
open Smt.Symbol

let a = AsciiSymbol.make_int 'a'
let b = AsciiSymbol.make_int 'b'
let x3 = AsciiSymbol.make_int 'c'
let x4 = AsciiSymbol.make_int 'd'

module Solver = Smt.Formula.Make_solver (struct
  include Overlays.Typed_z3
  let splits = [Splits.neq]
  let logics : (module Formula.LOGIC) list = [(module Difference)]
end)

let model_to_string model =
  Model.to_string model ~symbol:(fun uid -> uid |> Core.Char.of_int_exn |> AsciiSymbol.make_int)
    ~pp_assignment:(fun (I uid) v ->
      Printf.sprintf "%c => %d"
        (Core.Char.of_int_exn uid)
        v
    )

open Core
let () =
  let formula = Formula.And [
    Formula.Binop (Less_than, Key a, Const_int 0);
  ]
  in
  let result = Solver.solve [formula] in
  match result with
  | Solution.Sat model -> printf "%s\n" (model_to_string model)
  | Solution.Unsat -> printf "uh oh\n"
  | Solution.Unknown -> failwith "lol"
