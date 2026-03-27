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

let rec checks_out : type a k. (a, k) Formula.t -> a =
  function
  | Formula.Const_int i -> i
  | Const_bool b -> b
  | Binop (op, l, r) ->
      let f = Binop.to_arithmetic op in
      f (checks_out l) (checks_out r)
  | And ls ->
      List.for_all ls ~f:checks_out
  | Not x ->
      not (checks_out x)
  | f ->
      failwith ("can't evaluate whether that formula checks out: " ^ (Formula.to_string f))

let () =
  let mismatches = ref [] in

  Boolean.from_stdin ()
  |> fun ls -> List.iteri ls ~f:(fun i formula_text -> 
    let formula = Boolean.parse formula_text in

    let r1 = Solver_blue3.solve [formula] in
    let r2 = Solver_z3.solve [formula] in

    let tag1 = result_tag r1 in
    let tag2 = result_tag r2 in

    let is_bad =
      match r1, r2 with
      | Solution.Sat sol1, Solution.Sat _ ->
        let evaluated =
          try
            Formula.substitute formula sol1
            |> checks_out
          with _ -> false
        in
        not evaluated

      | _ -> not (String.equal tag1 tag2)
    in

    if is_bad then
      mismatches := {
        index = i;
        formula_text;
        blue3 = tag1;
        z3 = tag2;
      } :: !mismatches
  );

  (match !mismatches with
    | [] -> sprintf "✓ Blue3 checks out! (%d formulas)\n" (List.length ls)
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
