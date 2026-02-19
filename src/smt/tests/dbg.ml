[@@@ocaml.warning "-26"]
[@@@ocaml.warning "-27"]
[@@@ocaml.warning "-32"]

open Smt
open Smt.Symbol

let x1 = AsciiSymbol.make_int 'a'
let x2 = AsciiSymbol.make_int 'b'
let x3 = AsciiSymbol.make_int 'c'
let x4 = AsciiSymbol.make_int 'd'

let formula = Formula.And [
  Formula.Binop (
    Binop.Less_than_eq,
    Key x1,
    (
      Formula.Binop (
        Binop.Minus,
        Key x3,
        Const_int 5
      )
    )
  );
  Formula.Binop (
    Binop.Less_than_eq,
    Key x1,
    (
      Formula.Binop (
        Binop.Minus,
        Key x4,
        Const_int 3
      )
    )
  );
  Formula.Binop (
    Binop.Less_than_eq,
    Key x2,
    (
      Formula.Binop (
        Binop.Plus,
        Key x1,
        Const_int 3
      )
    )
  );
  Formula.Binop (
    Binop.Less_than_eq,
    Key x3,
    (
      Formula.Binop (
        Binop.Plus,
        Key x2,
        Const_int 2
      )
    )
  );
  Formula.Binop (
    Binop.Less_than_eq,
    Key x3,
    (
      Formula.Binop (
        Binop.Minus,
        Key x4,
        Const_int 1
      )
    )
  );
  Formula.Binop (
    Binop.Less_than_eq,
    Key x4,
    (
      Formula.Binop (
        Binop.Plus,
        Key x2,
        Const_int 5
      )
    )
  );
]

module Solver = Smt.Formula.Make_solver (Overlays.Typed_z3)
let () =
  let atoms = Diff.extract formula in
  let ls, map = Diff.normalize atoms in

  Printf.printf "Atoms:\n";
  Core.List.iter atoms ~f:(fun {Diff.x; y; c} ->
    Printf.printf "{ x = %d, y = %d, c = %d }\n" x y c
  );
  Printf.printf "Normal:\n";
  Core.List.iter ls ~f:(fun {Diff.x; y; c} ->
    Printf.printf "{ x = %d, y = %d, c = %d }\n" x y c
  );
  (* let solution = Solver.solve [formula] in *)
  (* match solution with *)
  (* | Solution.Sat model -> *)
  (*   Printf.printf "%s\n" ( *)
  (*     Model.to_string model ~symbol:(fun key -> key |> Char.chr |> AsciiSymbol.make_int) *)
  (*     ~pp_assignment:(fun (I x) v -> Printf.sprintf "%c => %d" (Char.chr x) v) *)
  (*   ) *)
  (* | _ -> *)
  (*   Printf.printf "UNSAT or UNKNOWN\n" *)
