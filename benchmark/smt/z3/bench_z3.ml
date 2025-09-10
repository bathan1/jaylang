open Z3
open Smt

let ctx = mk_context [("model","false")]

let time f =
    let t0 = Unix.gettimeofday () in
    f ();
    let t1 = Unix.gettimeofday () in
    t1 -. t0

(* Naive: directly assert all four constraints *)
let solver_naive () =
    let x = Arithmetic.Integer.mk_const_s ctx "x" in
    let y = Arithmetic.Integer.mk_const_s ctx "y" in
    let z0 = Arithmetic.Integer.mk_numeral_i ctx 0 in
    let z2 = Arithmetic.Integer.mk_numeral_i ctx 2 in
    let z5 = Arithmetic.Integer.mk_numeral_i ctx 5 in
    let s = Solver.mk_simple_solver ctx in
    Solver.add s [
        Arithmetic.mk_gt ctx x z0;                          (* x > 0 *)
        Arithmetic.mk_lt ctx x z5;                          (* x < 5 *)
        Boolean.mk_eq ctx x (Arithmetic.mk_add ctx [y; z2]);(* x = y + 2 *)
        Arithmetic.mk_ge ctx y z0;                          (* y >= 0 *)
    ];
    ignore (Solver.check s [] : Solver.status)

(* Simplified: y >= 0, y <= 2, and keep x = y + 2 *)
let solver_simplified () =
    let x = Arithmetic.Integer.mk_const_s ctx "x" in
    let y = Arithmetic.Integer.mk_const_s ctx "y" in
    let z0 = Arithmetic.Integer.mk_numeral_i ctx 0 in
    let z2 = Arithmetic.Integer.mk_numeral_i ctx 2 in
    let s = Solver.mk_simple_solver ctx in
    Solver.add s [
        Arithmetic.mk_ge ctx y z0;                          (* y >= 0 *)
        Arithmetic.mk_le ctx y z2;                          (* y <= 2 *)
        Boolean.mk_eq ctx x (Arithmetic.mk_add ctx [y; z2]);(* x = y + 2 *)
    ];
    ignore (Solver.check s [] : Solver.status)

let () =
    let t_naive = time solver_naive in
    let t_simpl = time solver_simplified in
    Printf.printf "naive:       %.6f s\nsimplified:  %.6f s\n%!"
        t_naive t_simpl

