open Core
open Smt
open Smt.Symbol
open Overlays
open Utils

let columns = [
  ["formula_id"; "INTEGER"; "PRIMARY KEY"];
  ["time_us_blue3"; "FLOAT"; "NOT NULL"];
  ["time_us_z3"; "FLOAT"; "NOT NULL"];
  ["is_backend_used"; "TEXT"; "NOT NULL"];
  ["is_sat"; "TEXT"; "NOT NULL"];
  ["formula_text_input"; "TEXT"; "NOT NULL"];
  ["formula_text_rewritten"; "TEXT"; "NOT NULL"];
  ["solution_text"; "TEXT"; "NOT NULL"];
]

module Solver_blue3 = Formula.Make_solver (Blue3)
module Solver_z3 = Formula.Make_solver (Typed_z3)

let sql_create_table =
  let column_stmts = columns
    |> List.map ~f:(String.concat ~sep:" ")
    |> String.concat ~sep:","
  in
  sprintf "CREATE TABLE IF NOT EXISTS comparisons (%s);" column_stmts

let bool_to_sql b = if b then "true" else "false"

let escape_sql s =
  String.concat_map s ~f:(fun c ->
    if Char.equal c '\'' then "''" else String.of_char c
  )

let () =
  let n_trials =
    match Sys.get_argv () with
    | [| _; n |] -> Int64.of_string n
    | _ ->
      eprintf "Usage: dune exec ./compare_z3.exe -- <n_trials> < formulas.txt\n";
      exit 1
  in

  eprintf "%s\n" sql_create_table;

  Boolean.from_stdin ()
  |> List.iteri ~f:(fun i formula_text ->
    let formula = Boolean.parse formula_text in
    let escaped_input = escape_sql formula_text in

    let rewritten_formula =
      formula
      |> Formula.rewrite
      |> fun (rewritten, _) -> Formula.to_string rewritten ~uid_to_string:(
          function
          | uid -> 
            uid
            |> Char.of_int_exn
            |> Char.to_string
        )
    in
    let escaped_rewritten = escape_sql rewritten_formula in

    let result_ref_blue3 = ref None in
    let result_ref_z3 = ref None in
    let backend_used_ref = ref false in

    let time_us_blue3 =
      Benchmarker.avg_latency_n
        n_trials
        ~label:"Blue3"
        ~f:(fun () ->
          Solver_blue3.is_backend_used := false;
          let r = Solver_blue3.solve [formula] in
          result_ref_blue3 := Some r;
          backend_used_ref := !Solver_blue3.is_backend_used
        )
    in

    let time_us_z3 =
      Benchmarker.avg_latency_n
        n_trials
        ~label:"Z3"
        ~f:(fun () ->
          let r = Solver_z3.solve [formula] in
          result_ref_z3 := Some r;
        )
    in

    let blue3_result =
      match !result_ref_blue3 with
      | Some r -> r
      | None -> failwith "blue3 solver never ran"
    in

    let is_sat =
      match blue3_result with
      | Solution.Sat _ -> true
      | _ -> false
    in

    let is_backend_used = !backend_used_ref in

    let solution_text =
      match blue3_result with
      | Solution.Sat model ->
          Model.json model
            ~symbol:(fun uid -> AsciiSymbol.make_int (Char.of_int_exn uid))
            ~key_of_symbol:(fun sym ->
              Symbol.X.extract sym
              |> Char.of_int_exn
              |> String.of_char
            )
            ~value_to_json:(fun v -> Int.to_string v)
          |> escape_sql
      | _ -> ""
    in

  eprintf
    "INSERT INTO comparisons VALUES (%d, %f, %f, '%s', '%s', '%s', '%s', '%s');\n"
    i
    time_us_blue3
    time_us_z3
    (bool_to_sql is_backend_used)
    (bool_to_sql is_sat)
    escaped_input
    escaped_rewritten
    solution_text
  )
