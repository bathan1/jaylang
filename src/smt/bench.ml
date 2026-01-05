[@@@ocaml.warning "-26"]
[@@@ocaml.warning "-32"]

open Core
open Overlays
open Smt
open Smt.Symbol

(* ---------- Symbols ---------- *)

let symbol = AsciiSymbol.make_int
let a = symbol 'a'
and b = symbol 'b'
and c = symbol 'c'
and d = symbol 'd'
and e = symbol 'e'

(* ---------- Solvers ---------- *)

module Backend_z3 = Formula.Make_solver (Typed_z3)

module Hybrid_z3 = Formula.Make_solver (struct
  include Typed_z3
  let logics : (module Formula.LOGIC) list = [
    (module Diff)
  ]
  let splits = [Splits.neq]
end)

(* ---------- Timing + Result ---------- *)

type 'k solver_result = {
  name   : string;
  time   : Time_ns.Span.t;
  result : 'k Solution.t;
}

let solve_with_time ~name solve expr =
  let start = Time_ns.now () in
  let result = solve [expr] in
  let time = Time_ns.(diff (now ()) start) in
  { name; time; result }

let print_result solver vars r =
  let time_str = Time_ns.Span.to_string_hum r.time in
  printf "%s:\n" solver;

  (match r.result with
   | Solution.Sat model ->
       printf "  SAT\n";
       Model.to_string model vars
         ~pp_assignment:(fun (I uid) v ->
           sprintf "    %c => %d" (Char.of_int_exn uid) v
         )
       |> printf "%s\n"
   | Solution.Unsat ->
       printf "  UNSAT\n"
   | Solution.Unknown ->
       printf "  UNKNOWN\n");

  printf "  Time: %s\n\n" time_str

let print_comparison r1 r2 =
  let open Time_ns.Span in
  let diff = abs (r1.time - r2.time) in
  let diff_str = to_string_hum diff in

  let winner =
    if r1.time < r2.time then r1.name
    else if r2.time < r1.time then r2.name
    else "Tie"
  in

  printf "🏁 Winner: %s (Δ %s)\n\n" winner diff_str

(* ---------- Test Expressions ---------- *)

let _exprs : (bool, int AsciiSymbol.t) Formula.t list = [

  (* 1 *)
  Binop (Equal, Key a, Const_int 123456);

  (* 2 *)
  Not (Binop (Equal, Key b, Key a));

  (* 3 *)
  And [
    Not (Binop (Equal, Key b, Key a));
    Binop (Equal, Key d, Key c);
  ];

  (* 4 *)
  And [
    Binop (Equal, Key a, Const_int 123456);
    Binop (Equal, Key b, Const_int 123456);
  ];

  (* 5 *)
  And [
    Binop (Equal, Key a, Const_int 123456);
    Not (Binop (Equal, Key b, Const_int 123456));
    Binop (Equal, Key c, Const_int 123456);
  ];

  (* 6 *)
  And [
    Binop (Equal, Key a, Const_int 123456);
    Binop (Equal, Key b, Const_int 123456);
    Binop (Equal, Key c, Const_int 123456);
  ];

  (* 7 *)
  And [
    Binop (Less_than, Key b, Key a);
    Not (Binop (Equal, Key c, Const_int 123456));
    Not (Binop (Equal, Key d, Const_int 123456));
    Binop (Equal, Key e, Const_int 123456);
  ];

  (* 8 *)
  And [
    Binop (Equal, Key a, Const_int 123456);
    Not (Binop (Equal, Key b, Const_int 123456));
    Binop (Equal, Key c, Const_int 123456);
    Binop (Equal, Key d, Const_int 123456);
  ];

  (* 9 *)
  And [
    Binop (Equal, Key a, Const_int 123456);
    Binop (Equal, Key b, Const_int 123456);
    Not (Binop (Equal, Key c, Const_int 123456));
    Binop (Equal, Key d, Const_int 123456);
  ];

  (* 10 *)
  And [
    Binop (Equal, Key a, Const_int 123456);
    Binop (Equal, Key b, Const_int 123456);
    Binop (Equal, Key c, Const_int 123456);
    Binop (Equal, Key d, Const_int 123456);
  ];
]

(* ---------- Main ---------- *)

(* let () = *)
(*   Boolean.from_stdin () *)
(*   |> List.map ~f:Boolean.parse *)
(*   |> List.iteri ~f:(fun i expr -> *)
(*        printf "====================================\n"; *)
(*        printf "(%d) %s\n\n" *)
(*          (i + 1) *)
(*          (Formula.to_string expr *)
(*             ~key:(fun uid -> *)
(*               uid |> Char.of_int_exn |> Char.to_string)); *)
(**)
(*        let hybrid = *)
(*          solve_with_time *)
(*            ~name:"Hybrid" *)
(*            Hybrid_z3.solve *)
(*            expr *)
(*        in *)
(**)
(*        let backend = *)
(*          solve_with_time *)
(*            ~name:"Backend" *)
(*            Backend_z3.solve *)
(*            expr *)
(*        in *)
(**)
(*        print_result "Hybrid" [a; b; c; d; e] hybrid; *)
(*        print_result "Backend" [a; b; c; d; e] backend; *)
(**)
(*        print_comparison hybrid backend *)
(*      ) *)

let () =
  let formulae = Boolean.from_stdin () in
  Stdlib.List.iteri
    (fun idx f ->
      try
        let ast = Boolean.parse f in
  print_endline (Formula.to_string ~key:Boolean.stringify ast);
        let result = Hybrid_z3.solve [ast] in
        match result with
        | Solution.Sat model ->
            Printf.printf "SAT\n";
            let vars = (
              Core.List.map model.keys ~f:(fun uid ->
                uid |> Core.Char.of_int_exn |> AsciiSymbol.make_int
              )
            )
            in
            Model.to_string model vars
              ~pp_assignment:(fun (I uid) v ->
                Printf.sprintf "    %c => %d" (Core.Char.of_int_exn uid) v
              )
            |> Printf.printf "%s\n"
        | Solution.Unsat ->
            Printf.printf "UNSAT\n"
        | Solution.Unknown ->
            Printf.printf "UNKNOWN\n";
    with
    | Boolean.Lex_error (pos, msg) ->
        Printf.eprintf
          "[error] formula %d: lex error at %d: %s\n  input: %s\n"
          (idx + 1) pos msg f
    | Boolean.Parse_error (pos, msg) ->
        Printf.eprintf
          "[error] formula %d: parse error at %d: %s\n  input: %s\n"
          (idx + 1) pos msg f
    | exn ->
        Printf.eprintf
          "[error] formula %d: %s\n  input: %s\n"
          (idx + 1) (Stdlib.Printexc.to_string exn) f)
  formulae
