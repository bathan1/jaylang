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
        Const_int (5)
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
        Const_int (3)
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
        Const_int (1)
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

module Solver = Smt.Formula.Make_solver (struct
  include Overlays.Typed_z3
  let splits = [Splits.neq]
  let logics : (module Formula.LOGIC) list = [(module Difference)]
end)

module Checker = Smt.Formula.Make_solver (Overlays.Typed_z3)
let () =
  (* let atoms = Diff.extract formula in *)
  (* let vertices, edges, map = Diff.normalize atoms in *)
  (* let distances, _ = Diff.bellman_ford vertices edges ~src:0 *)
  (* in *)
  (* let open Core in *)
  (* Printf.printf "Atoms:\n"; *)
  (* Core.List.iter atoms ~f:(fun {Diff.x; y; c} -> *)
  (*   Printf.printf "{ x = %d, y = %d, c = %d }\n" x y c *)
  (* ); *)
  (* Printf.printf "Normal:\n"; *)
  (* Core.Array.iter edges ~f:(fun (x, y, c) -> *)
  (*   Printf.printf "x%d <= x%d%s\n" x y (if c < 0 then " - " ^ (Int.to_string (-c)) else " + " ^ (Int.to_string c)) *)
  (* ); *)
  (* let distance_ls = List.of_array distances in *)
  (* printf "Distances: %s\n" (List.to_string distance_ls ~f:(function *)
  (*   | None -> "disconnected" *)
  (*   | Some v -> Int.to_string v *)
  (* )); *)

  (* let solution = Solver.solve [formula] in *)
  (* match solution with *)
  (* | Solution.Sat model -> *)
  (*   Printf.printf "%s\n" ( *)
  (*     Model.to_string model ~symbol:(fun key -> key |> Char.chr |> AsciiSymbol.make_int) *)
  (*     ~pp_assignment:(fun (I x) v -> Printf.sprintf "%c => %d" (Char.chr x) v) *)
  (*   ); *)
  (**)
  (*   let subbed = Formula.substitute formula model in *)
  (*   let text = Formula.to_string subbed in *)
  (*   Printf.printf "%s\n" text; *)
  (**)
  (*   let z3_result = Checker.solve [subbed] in *)
  (*   begin match z3_result with *)
  (*     | Solution.Sat _ -> print_endline "OK!"; *)
  (*     | Solution.Unsat -> print_endline "UNSAT\n"; *)
  (*     | Solution.Unknown -> print_endline "UNKNOWN\n"; *)
  (*     end *)
  (* | _ -> *)
  (*   Printf.printf "UNSAT or UNKNOWN\n" *)
  let pp_model = fun model ->
    Model.to_string model ~symbol:(fun uid -> uid |> Core.Char.of_int_exn |> AsciiSymbol.make_int)
      ~pp_assignment:(fun (I uid) v ->
        Printf.sprintf "%c => %d"
          (Core.Char.of_int_exn uid) v
      )
  in
  let formulae = Boolean.from_stdin () in
  let escape_csv s =
    let s = Core.String.concat ~sep:" " (Core.String.split_lines s) in
    "\"" ^ Core.String.escaped s ^ "\""
  in

  Printf.printf "index,expected,actual,status,formula,model,substituted,error\n";

  List.iteri
    (fun idx input ->
      try
        let ast = Boolean.parse input in
        let formula_text = Formula.to_string ast in

        let expected = Checker.solve [ast] in
        let own_result = Solver.solve [ast] in

        let expected_str =
          match expected with
          | Solution.Sat _ -> "SAT"
          | Solution.Unsat -> "UNSAT"
          | Solution.Unknown -> "UNKNOWN"
        in

        let actual_str =
          match own_result with
          | Solution.Sat _ -> "SAT"
          | Solution.Unsat -> "UNSAT"
          | Solution.Unknown -> "UNKNOWN"
        in

        match expected, own_result with

        (* ---------------- MATCH CASES ---------------- *)

        | Solution.Unsat, Solution.Unsat ->
          Printf.printf "%d,%s,%s,OK,%s,,,\n"
            idx expected_str actual_str (escape_csv formula_text)

        | Solution.Sat _, Solution.Sat model ->
          let subbed = Formula.substitute ast model in
          begin match Checker.solve [subbed] with
            | Solution.Sat _ ->
              Printf.printf "%d,%s,%s,OK,%s,%s,%s,\n"
                idx expected_str actual_str
                (escape_csv formula_text)
                (escape_csv (pp_model model))
                (escape_csv (Formula.to_string subbed))

            | Solution.Unsat ->
              Printf.printf "%d,%s,%s,MISMATCH,%s,%s,%s,Incorrect model\n"
                idx expected_str actual_str
                (escape_csv formula_text)
                (escape_csv (pp_model model))
                (escape_csv (Formula.to_string subbed))

            | Solution.Unknown ->
              Printf.printf "%d,%s,%s,ERROR,%s,%s,%s,Z3 could not validate substitution\n"
                idx expected_str actual_str
                (escape_csv formula_text)
                (escape_csv (pp_model model))
                (escape_csv (Formula.to_string subbed))
            end

        (* ---------------- MISMATCH CASES ---------------- *)

        | Solution.Unsat, Solution.Sat model ->
          Printf.printf "%d,%s,%s,MISMATCH,%s,%s,,Expected UNSAT but got SAT\n"
            idx expected_str actual_str
            (escape_csv formula_text)
            (escape_csv (pp_model model))

        | Solution.Sat _, Solution.Unsat ->
          Printf.printf "%d,%s,%s,MISMATCH,%s,,,%s\n"
            idx expected_str actual_str
            (escape_csv formula_text)
            "Expected SAT but got UNSAT"

        | Solution.Unknown, _ ->
          Printf.printf "%d,%s,%s,ERROR,%s,,,%s\n"
            idx expected_str actual_str
            (escape_csv formula_text)
            "Z3 returned UNKNOWN"

        | _, Solution.Unknown ->
          Printf.printf "%d,%s,%s,ERROR,%s,,,%s\n"
            idx expected_str actual_str
            (escape_csv formula_text)
            "Own solver returned UNKNOWN"

      with e ->
        Printf.printf "%d,,,,,,,%s\n"
          idx
          (escape_csv (Core.Exn.to_string e))
    )
    formulae;

