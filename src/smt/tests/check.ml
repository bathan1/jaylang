open Core
open Smt
open Overlays

module Solver_blue3 = Formula.Make_solver (Blue3)
module Solver_z3 = Formula.Make_solver (Typed_z3)

type mismatch = {
  index : int;
  formula_text : string;
  blue3 : string;
  z3 : string;
}

let result_tag = function
  | Solution.Sat _ -> "SAT"
  | Solution.Unsat -> "UNSAT"
  | Solution.Unknown -> "UNKNOWN"

let () =
  let mismatches = ref [] in

  Boolean.from_stdin ()
  |> List.iteri ~f:(fun i formula_text -> 
    let formula = Boolean.parse formula_text in

    let r1 = Solver_blue3.solve [formula] in
    let r2 = Solver_z3.solve [formula] in

    let tag1 = result_tag r1 in
    let tag2 = result_tag r2 in

    if not (String.equal tag1 tag2) then
      mismatches := {
        index = i;
        formula_text;
        blue3 = tag1;
        z3 = tag2;
      } :: !mismatches
  );

  (match !mismatches with
    | [] -> "√ Blue3 checks out!\n"
    | ls ->  
      ls
      |> List.rev
      |> List.fold ~init:"" ~f:(fun acc m ->
        sprintf "%s\n[%d]\nFormula:%s\nBlue3: %s\nZ3: %s\n" 
        acc
        m.index
        m.formula_text
        m.blue3
        m.z3
      ))
  |> printf "%s"
