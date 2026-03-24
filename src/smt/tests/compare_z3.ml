open Core
open Smt
open Overlays
open Utils

let columns = [
  ["formula_id"; "INTEGER"; "PRIMARY KEY"];
  ["time_us_blue3"; "FLOAT"; "NOT NULL"];
  ["time_us_z3"; "FLOAT"; "NOT NULL"];
  ["is_backend_used"; "TEXT"; "NOT NULL"];
  ["is_sat"; "TEXT"; "NOT NULL"];
  ["formula_text"; "TEXT"; "NOT NULL"];
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
    let result_ref_blue3 = ref None in
    let result_ref_z3 = ref None in
    let backend_used_ref = ref false in
    let time_us_blue3 = Benchmarker.avg_latency_n
      n_trials
      ~label:"Blue3"
      ~f:(fun () ->
        Solver_blue3.is_backend_used := false;
        let r = Solver_blue3.solve [formula] in
        result_ref_blue3 := Some r;
        backend_used_ref := !Solver_blue3.is_backend_used
      )
    in
    let time_us_z3 = Benchmarker.avg_latency_n
      n_trials
      ~label:"Z3"
      ~f:(fun () ->
        let r = Solver_z3.solve [formula] in
        result_ref_z3 := Some r;
      )
    in
    let is_sat = match !result_ref_blue3 with
      | Some r -> r |>
        (function
        | Solution.Sat _ -> true
        | _ -> false)
      | None -> failwith "blue3 solver never ran"
    in
    let is_backend_used = !backend_used_ref in
    (* Escape single quotes in formula text for SQL *)
    let escaped_formula = String.concat_map formula_text ~f:(fun c ->
      if Char.equal c '\'' then "''" else String.of_char c
    ) in
    eprintf "INSERT INTO comparisons VALUES (%d, %f, %f, '%s', '%s', '%s');\n"
      i
      time_us_blue3
      time_us_z3
      (bool_to_sql is_backend_used)
      escaped_formula
      (bool_to_sql is_sat)
  )
