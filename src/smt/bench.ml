open Core
open Overlays
open Smt

module Backend_z3 = Formula.Make_solver(Typed_z3)

module Hybrid_z3 = Formula.Make_solver (struct
  include Typed_z3
  let logics : (module Formula.LOGIC) list = [
    (module Diff)
  ]
end)

module AsciiSymbol = Smt.Symbol.Make (struct
  type t = char

  let uid = Stdlib.Char.code
end)

let run_hybrid expr (vars : int AsciiSymbol.t list) ~i =
  let start_time = Time_ns.now () in
  printf "(%d) Hybrid solve on: %s\n"
    i
    (Formula.to_string expr ~key:(fun uid _is_bool ->
       uid |> Char.of_int_exn |> Char.to_string));

  let result = Hybrid_z3.solve [expr] in

  let duration = Time_ns.(diff (now ()) start_time) in
  let duration_str = Time_ns.Span.to_string_hum duration in

  (* print the result *)
  (match result with
   | Solution.Sat model ->
      Model.to_string model vars ~pp_assignment:(
        fun (I uid) v -> sprintf "  %c => %d" (Char.of_int_exn uid) v
      )
      |> printf "SAT:\n%s\n";
   | Solution.Unsat -> printf "UNSAT\n"
   | Solution.Unknown -> printf "UNKNOWN\n");

  printf "⏱  Solve time: %s\n\n" duration_str

let run_backend expr (vars : int AsciiSymbol.t list) ~i =
  let start_time = Time_ns.now () in

  printf "(%d) Backend solve on: %s\n"
    i
    (Formula.to_string expr ~key:(fun uid _is_bool ->
       uid |> Char.of_int_exn |> Char.to_string));

  let result = Backend_z3.solve [expr] in

  let duration = Time_ns.(diff (now ()) start_time) in
  let duration_str = Time_ns.Span.to_string_hum duration in

  (* print the result *)
  (match result with
   | Solution.Sat model ->
        Model.to_string model vars ~pp_assignment:(
          fun (I uid) v -> sprintf "  %c => %d" (Char.of_int_exn uid) v
        )
        |> printf "SAT:\n%s\n";
   | Solution.Unsat -> printf "UNSAT\n"
   | Solution.Unknown -> printf "UNKNOWN\n");

  printf "⏱  Solve time: %s\n\n" duration_str

let _ =
  "
  1. (a = 123456)
  2. (not (b = a))
  3. (not (b = a)) ^ (d = c)
  4. (a = 123456) ^ (b = 123456)
  5. (a = 123456) ^ (not (b = 123456)) ^ (c = 123456)
  6. (a = 123456) ^ (b = 123456) ^ (c = 123456)
  7. (b < a) ^ (not (c = 123456)) ^ (not (d = 123456)) ^ (e = 123456)
  8. (a = 123456) ^ (not (b = 123456)) ^ (c = 123456) ^ (d = 123456)
  9. (a = 123456) ^ (b = 123456) ^ (not (c = 123456)) ^ (d = 123456)
  10. (a = 123456) ^ (b = 123456) ^ (c = 123456) ^ (d = 123456)"

let symbol = AsciiSymbol.make_int
let a = symbol 'a' and b = symbol 'b'
and c = symbol 'c' and d = symbol 'd'
and e = symbol 'e'

let exprs : (bool, int AsciiSymbol.t) Formula.t list = [
  (* 1 *)
  Binop (Equal, Key a, Const_int 123456);

  (* 2 *)
  Not (Binop (Equal, Key a, Key b));

  (* 3 *)
  And [
    Not (Binop (Equal, Key b, Key a));
    Binop (Equal, Key d, Key c)
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

let () =
  exprs
  |> List.iteri ~f:(fun i expr -> run_hybrid ~i:(i + 1) expr [a; b; c; d; e]; run_backend ~i:(i + 1) expr [a; b; c; d; e;] )
