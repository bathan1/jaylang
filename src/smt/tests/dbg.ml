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
  let logics : (module Formula.LOGIC) list = [(module Diff)]
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
  (* (not ((a + 1) >= 0)) ^ (a <= 0) *)
  let formula = Formula.And [
    Not (
      Binop (
        Greater_than_eq,
        (Binop (Plus, Key a, Const_int 1)),
        Const_int 0
      )
    )
  ]
  in
  let extracted = Diff.extract formula in
  List.iter extracted ~f:(fun {x; y; c;} -> (
    printf "%c <= %c%s\n" (Char.of_int_exn x) (Char.of_int_exn y) (if c < 0 then " - " ^ Int.to_string (-c) else " + " ^ Int.to_string c)
  ));
  let result = Solver.solve [formula] in
  match result with
  | Solution.Sat model -> printf "%s\n" (model_to_string model)
  | Solution.Unsat -> printf "uh oh\n"
  | Solution.Unknown -> failwith "lol"
