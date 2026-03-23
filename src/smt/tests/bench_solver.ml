[@@@ocaml.warning "-26"]
[@@@ocaml.warning "-27"]
[@@@ocaml.warning "-32"]
open Core
open Smt
open Smt.Symbol
open Overlays
module Solver = Formula.Make_solver (Blue3)
(* ---------- Helpers ---------- *)
let symbol = AsciiSymbol.make_int
let char_of_uid uid =
  Char.of_int_exn uid
let uid_of_char c =
  Char.to_int c
let sql_escape s =
  "'" ^ String.concat ~sep:"''" (String.split s ~on:'\'') ^ "'"
let model_to_map (model : 'k Model.t) : bool Map.M(Char).t =
  List.fold model.keys ~init:(Map.empty (module Char)) ~f:(fun acc uid ->
    let sym = AsciiSymbol.make_int (Char.of_int_exn uid) in
    match model.value sym with
    | Some v ->
      Map.set acc
        ~key:(char_of_uid uid)
        ~data:(v = 1)
    | None ->
      acc
  )
let max_var_in_string s =
  String.fold s ~init:'a' ~f:(fun acc c ->
    if Char.(c >= 'a' && c <= 'z') then Char.max acc c else acc
  )
(* ---------- Main ---------- *)
let () =
  let n_trials =
    match Sys.get_argv () with
    | [| _; n |] -> Int64.of_string n
    | _ ->
      eprintf "Usage: bench <n_trials> < formulas.txt\n";
      exit 1
  in
  let formulae = Boolean.from_stdin () in
  let parsed =
    List.mapi formulae ~f:(fun idx input ->
      try
        let ast = Boolean.parse input in
        let formula_text = Formula.to_string ast in
        Ok (idx, input, ast, formula_text)
      with
        | exn ->
        eprintf "[error] formula %d: %s\n" (idx + 1) (Exn.to_string exn);
        Error ()
    )
    |> List.filter_map ~f:(function Ok x -> Some x | Error _ -> None)
  in
  let global_max_var =
    List.fold parsed ~init:'a' ~f:(fun acc (_, _, _, formula_text) ->
      Char.max acc (max_var_in_string formula_text)
    )
  in
  let all_vars =
    List.init (Char.to_int global_max_var - Char.to_int 'a' + 1)
      ~f:(fun i -> Char.of_int_exn (Char.to_int 'a' + i))
  in
  (* ---------- CREATE TABLE ---------- *)
  eprintf "CREATE TABLE IF NOT EXISTS benchmarks (\n";
  eprintf "  formula_id       INTEGER PRIMARY KEY,\n";
  eprintf "  original_formula TEXT    NOT NULL,\n";
  eprintf "  time_to_solve_us REAL    NOT NULL,\n";
  eprintf "  is_backend_used  TEXT    NOT NULL,\n";
  eprintf "  is_sat           TEXT    NOT NULL";
  List.iter all_vars ~f:(fun c ->
    eprintf ",\n  var_%c            INTEGER" c
  );
  eprintf "\n);\n\n";
  (* ---------- INSERT ROWS ---------- *)
  List.iter parsed ~f:(fun (idx, _input, ast, formula_text) ->
    let result_ref = ref None in
    let backend_used_ref = ref false in
    let samples =
      Benchmark.latencyN
        n_trials
        [ ("solver",
            (fun () ->
              Solver.is_backend_used := false;
              let r = Solver.solve [ast] in
              result_ref := Some r;
              backend_used_ref := !Solver.is_backend_used),
            ())
        ]
    in
    let time_us =
      match samples with
      | [ (_, [ t ]) ] ->
        t.Benchmark.wall *. 1_000_000.0 /. Int64.to_float n_trials
      | _ -> failwith "Unexpected latencyN output"
    in
    let result =
      match !result_ref with
      | Some r -> r
      | None -> failwith "No result captured"
    in
    let model_map =
      match result with
      | Solution.Sat model -> model_to_map model
      | _ -> Map.empty (module Char)
    in
    let is_sat = match result with Solution.Sat _ -> 1 | _ -> 0 in
    let backend_used = !backend_used_ref in
    eprintf "INSERT INTO benchmarks (formula_id, original_formula, time_to_solve_us, is_backend_used, is_sat";
    List.iter all_vars ~f:(fun c -> eprintf ", var_%c" c);
    eprintf ")\nVALUES (%d, %s, %.3f, '%s', '%s'"
      (idx + 1)
      (sql_escape formula_text)
      time_us
      (if backend_used then "true" else "false")
      (if is_sat = 1 then "true" else "false");
    List.iter all_vars ~f:(fun c ->
      match Map.find model_map c with
      | Some true  -> eprintf ", 1"
      | Some false -> eprintf ", 0"
      | None       -> eprintf ", NULL"
    );
    eprintf ");\n";
  )
