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

let vars_of_model (model : 'k Model.t) =
  Core.List.map model.keys ~f:(fun uid ->
    uid |> Core.Char.of_int_exn |> AsciiSymbol.make_int
  )

let model_to_string model =
  Model.to_string model (vars_of_model model)
    ~pp_assignment:(fun (I uid) v ->
      Printf.sprintf "%c => %d"
        (Core.Char.of_int_exn uid)
        v
    )

(* ---------- Timing + Result ---------- *)

type 'k solver_result = {
  name   : string;
  time   : Time_ns.Span.t;
  result : 'k Solution.t;
}

let us_of_span (t : Time_ns.Span.t) : float =
  Time_ns.Span.to_us t

let csv_escape (s : string) : string =
  "\"" ^ String.concat ~sep:"\"\"" (String.split s ~on:'"') ^ "\""

let print_csv_row
    ~id
    ~formula_text
    ~solution
    ~model_text
    ~hybrid
    ~backend
  =
  let h_us = us_of_span hybrid.time in
  let b_us = us_of_span backend.time in
  let diff = h_us -. b_us in
  let is_winner = if Stdlib.(<) diff 0.0 then 1 else 0 in

  printf "%d,%s,%s,%s,%.3f,%.3f,%d,%.3f\n"
    id
    (csv_escape formula_text)
    (csv_escape solution)
    (csv_escape model_text)
    h_us
    b_us
    is_winner
    diff



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

let warmup_formula = Formula.Const_bool true

let warmup () =
  let _ =
    Hybrid_z3.solve [warmup_formula]
  in
  let _ =
    Backend_z3.solve [warmup_formula]
  in
  ()

let () =
  (* --- CSV header --- *)
  printf
    "id,formula_text,solution_text,model_text,hybrid_time,backend_only_time,is_hybrid_winner,hybrid_time_diff\n";

  warmup ();

  let formulae = Boolean.from_stdin () in

  Stdlib.List.iteri
    (fun idx input ->
      try
        (* --- Parse --- *)
        let ast = Boolean.parse input in

        let formula_text =
          Formula.to_string ast ~key:Boolean.stringify
        in

        (* --- Solve with Hybrid --- *)
        let hybrid =
          solve_with_time
            ~name:"Hybrid"
            Hybrid_z3.solve
            ast
        in

        (* --- Solve with Backend --- *)
        let backend =
          solve_with_time
            ~name:"Backend"
            Backend_z3.solve
            ast
        in

        (* --- Prefer vars from Hybrid model --- *)
        let vars =
          match hybrid.result with
          | Solution.Sat model when not (List.is_empty model.keys) ->
              vars_of_model model
          | _ ->
              []
        in

        (* --- Solution text --- *)
        let solution_text =
          match hybrid.result with
          | Solution.Sat _ -> "SAT"
          | Solution.Unsat -> "UNSAT"
          | Solution.Unknown -> "UNKNOWN"
        in

        (* --- Model text (nullable) --- *)
        let model_text =
          match hybrid.result with
          | Solution.Sat model ->
              Model.to_string model vars
                ~pp_assignment:(fun (I uid) v ->
                  Printf.sprintf "%c => %d"
                    (Char.of_int_exn uid) v
                )
          | _ -> ""
        in

        (* --- Timing + comparison --- *)
        let h_us = us_of_span hybrid.time in
        let b_us = us_of_span backend.time in
        let diff = h_us -. b_us in
        let is_winner = if Stdlib.(<) h_us b_us then 1 else 0 in

        (* --- CSV row --- *)
        printf "%d,%s,%s,%s,%.3f,%.3f,%d,%.3f\n"
          (idx + 1)
          (csv_escape formula_text)
          (csv_escape solution_text)
          (csv_escape model_text)
          h_us
          b_us
          is_winner
          diff

      with
      | Boolean.Lex_error (pos, msg) ->
          Printf.eprintf
            "[error] formula %d: lex error at %d: %s\n  input: %s\n"
            (idx + 1) pos msg input

      | Boolean.Parse_error (pos, msg) ->
          Printf.eprintf
            "[error] formula %d: parse error at %d: %s\n  input: %s\n"
            (idx + 1) pos msg input

      | exn ->
          Printf.eprintf
            "[error] formula %d: %s\n  input: %s\n"
            (idx + 1)
            (Stdlib.Printexc.to_string exn)
            input
    )
    formulae

