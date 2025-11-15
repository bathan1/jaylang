open Core
open Overlays

module AsciiSymbol = Smt.Symbol.Make (struct
  type t = char

  let uid = Stdlib.Char.code
end)

module HybridSolver = Smt.Formula.Make_solver (Typed_z3)

let () =
  let open Printf in
  (* --- Make symbols --- *)
  let a = AsciiSymbol.make_int 'a' in
  let b = AsciiSymbol.make_int 'b' in
  (**)
  (* (* --- Build the formula pieces --- *) *)
  (* let b_is_even = *)
  (*   Smt.Formula.Binop (Equal, Binop (Modulus, Key b, Const_int 2), Const_int 0) *)
  (* in *)
  (**)
  (* let a_gte_5 = Smt.Formula.Binop (Less_than_eq, Key a, Const_int 5) in *)
  (**)
  (* let b_lt_a = Smt.Formula.Binop (Less_than, Key b, Key a) in *)
  (**)
  (* let b_gt_a_minus_3 = *)
  (*   Smt.Formula.Binop *)
  (*     (Greater_than, Key b, Smt.Formula.Binop (Minus, Key a, Const_int 3)) *)
  (* in *)

  let exprs : (bool, 'k) Smt.Formula.t list =
    [ 
      Smt.Formula.Binop (Equal, Key a, Const_int 123456); 
      Smt.Formula.Binop (Greater_than_eq, Key a, Const_int 1) 
    ]
    (* [ b_is_even; a_gte_5; b_lt_a; b_gt_a_minus_3 ] *)
  in

  let solution = HybridSolver.solve exprs in

  match solution with
  | Sat model ->
      printf "MODEL FROM HYBRID SOLVER (IDL upper bounds applied):\n" ;
      List.iter [ a; b ] ~f:(fun key ->
          match model.value key with
          | Some v ->
              printf "  %c = %d\n"
                (Stdlib.Char.chr (Smt.Symbol.X.extract key))
                v
          | None ->
              printf "  %c = <unassigned>\n"
                (Stdlib.Char.chr (Smt.Symbol.X.extract key)))
  | Unsat -> printf "UNSAT\n"
  | Unknown -> printf "UNKNOWN\n"
