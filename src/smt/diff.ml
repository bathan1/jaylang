(* We include this specific implementation of [Formula.LOGIC] since
   a large number of expressions the cevaluator generates
   can be simplified / solved using Integer Difference Logic. *)
open Core

(** Encodes the relation [X - Y <= C], or equivalently, [X <= Y + C].
    The IDL logic itself supports {i any} of the following binary operators:
    {ol
      {-[=]}
      {-[<>] (structural inequality for us)}
      {-[<]}
      {-[<=]}
      {-[>=]}
      {-[>]} }
    This module normalizes all inputs into [<=] relations. *)
type atom = {
  (** Variable (id) to subtract. *)
  x : int;

  (** Variable (id) that subtracts [x]. *)
  y : int;

  (** Intepreted as an int {i literal} *)
  c : int;
};;

(** Transforms FORMULA into atoms if FORMULA is an And {!Formula.t}.
    Otherwise, it returns an empty list.

    {3 Example}
    {[
    let () =
      Diff.extract (And [
        Binop (Less_than_eq, Key a, Key b);
        Binop (Less_than_eq, Key c, Key d);
      ])
      |> fun ls -> printf "%d\n" (List.length ls)
      (* Prints: 2 *)
    ]}
*)
let rec extract (formula : (bool, 'k) Formula.t) : atom list =
  formula
  |> function
    (* x = c -> (x - y <= c) and (0 - x) <= -c *)
  | Binop (Equal, Key I x, Const_int c)
  | Binop (Equal, Const_int c, Key I x) ->
    [ { x; y = 0; c; };
      {x = 0; y = x; c = -c } ]

    (* x = y -> (x - y) <= 0 and (y - x) <= 0*)
  | Binop (Equal, Key I x, Key I y) ->
    [ { x; y; c = 0 };
      { x = y; y = x; c = 0 } ]

    (* x <= y -> (x - y <= 0)
        y >= x -> (x - y <= 0)
        not (x > y) -> x <= y -> (x - y) <= 0 *)
  | Binop (Less_than_eq, Key I x, Key I y)
  | Binop (Greater_than_eq, Key I y, Key I x)
  | Not Binop (Less_than, Key I y, Key I x)
  | Not Binop (Greater_than, Key I x, Key I y) ->
    [{ x; y; c = 0 }]

    (* x <= c -> (x - 0) <= c
        c >= x -> (x - 0) <= c
        not (x > c) -> x <= c -> (x - 0) <= c *)
  | Binop (Less_than_eq, Key I x, Const_int c)
  | Binop (Greater_than_eq, Const_int c, Key I x)
  | Not Binop (Less_than, Const_int c, Key I x)
  | Not Binop (Greater_than, Key I x, Const_int c) ->
    [{ x; y = 0; c }]

    (* x < c -> x - 0 <= c - 1 *)
  | Binop (Less_than, Key I x, Const_int c)
  | Binop (Greater_than, Const_int c, Key I x)
  | Not Binop (Less_than_eq, Const_int c, Key I x)
  | Not Binop (Greater_than_eq, Key I x, Const_int c) ->
    [{ x; y = 0; c = c - 1 }]

    (* x >= c -> 0 - x <= -c
       not (x < c) -> x >= c -> (0 - x) <= -c *)
  | Binop (Greater_than_eq, Key I x, Const_int c)
  | Binop (Less_than_eq, Const_int c, Key I x)
  | Not Binop (Greater_than, Const_int c, Key I x)
  | Not Binop (Less_than, Key I x, Const_int c) ->
    [ {x = 0; y = x; c = -c}  ]

  (* x > c -> (0 - x) <= -(c + 1) *)
  | Binop (Greater_than, Key I x, Const_int c)
  | Binop (Less_than, Const_int c, Key I x)
  | Not Binop (Greater_than_eq, Const_int c, Key I x)
  | Not Binop (Less_than_eq, Key I x, Const_int c) ->
    [{ x = 0; y = x; c = -(c + 1) }]

  | Formula.And exprs ->
    exprs
    |> List.map ~f:extract
    |> List.concat
  | _ -> []
;;

(** Search for the tightest upper bounds of each unique [x, y] variable in ATOMS.
    This is {i decidable}, so it only returns SAT or UNSAT (no unknown cases).

    {3 Example}
    {[
    let () =
      let atoms = [
        Diff.atom ~x:0 ~y:1 ~c:3;   (* x - y <= 3 *)
        Diff.atom ~x:1 ~y:Const ~c:10;  (* y <= 10 *)
      ] in

      match solve atoms with
      | Sat model ->
          (* Access a (tight) upper bound: model.value (I 0) -> int option *)
          printf "SAT: upper bound on x = %d\n"
            (Option.value_exn (model.value (I 0)))
      | Unsat ->
          printf "UNSAT\n"
    ]}
*)
let solve (atoms : atom list) : 'k Solution.t =
  let vars =
    List.fold atoms ~init:Int.Set.empty ~f:(fun acc {x; y; _} ->
      Set.add (Set.add acc x) y)
  in
  let edges =
    List.fold atoms ~init:Int.Map.empty ~f:(fun m {x; y; c} ->
      let lst = Map.find m y |> Option.value ~default:[] in
      Map.set m ~key:y ~data:((x, c) :: lst))
  in
  let dist =
    Set.fold vars ~init:Int.Map.empty ~f:(fun m v ->
      let inf = Int.max_value / 4 in
      let initial = if v = 0 then 0 else inf in
      Map.set m ~key:v ~data:initial)
  in
  let in_queue =
    Set.fold vars ~init:(Int.Table.create ()) ~f:(fun tbl v ->
      Hashtbl.set tbl ~key:v ~data:false; tbl)
  in
  let relax =
    Set.fold vars ~init:(Int.Table.create ()) ~f:(fun tbl v ->
      Hashtbl.set tbl ~key:v ~data:0; tbl)
  in
  let q = Queue.create () in
  Set.iter vars ~f:(fun v ->
    Queue.enqueue q v;
    Hashtbl.set in_queue ~key:v ~data:true
  );
  let rec loop dist =
    if Queue.is_empty q then
      Solution.Sat (
        Model.of_local dist ~lookup:Map.find
      )
    else begin
      let u = Queue.dequeue_exn q in
      Hashtbl.set in_queue ~key:u ~data:false;

      let dist_u = Map.find_exn dist u in
      let outgoing = Map.find edges u |> Option.value ~default:[] in

      let process_edge (dist, found_cycle) (v, w) =
        let dist_v = Map.find_exn dist v in
        let candidate = dist_u + w in
        if candidate < dist_v then begin
          let dist = Map.set dist ~key:v ~data:candidate in
          let cnt = (Hashtbl.find_exn relax v) + 1 in
          if cnt > Set.length vars then
            (dist, true)
          else begin
            Hashtbl.set relax ~key:v ~data:cnt;
            if not (Hashtbl.find_exn in_queue v) then begin
              Queue.enqueue q v;
              Hashtbl.set in_queue ~key:v ~data:true
              end;
            (dist, false)
            end
          end else
          (dist, found_cycle)
      in

      let (dist', cycle_found) =
        List.fold outgoing ~init:(dist, false) ~f:process_edge
      in

      if cycle_found then Unsat
      else loop dist'
      end
  in

  loop dist
;;

(** Propagate MODEL into FORMULA to spit out a new residual [Formula].

    {3 Example}
    {[
    open Smt
    open Smt.Symbol

    let symbol = AsciiSymbol.make_int
    let a = symbol 'a' and b = symbol 'b'
    let () =
      (* (a >= 5) AND (b < a) *)
      let formula =
          Formula.And
          [
            Binop (Greater_than_eq, Key a, Const_int 5);
            Binop (Less_than, Key b, Key a);
          ]
      in
      let model = Model.of_local 0 ~lookup:(fun _ uid ->
        uid
        |> function
          | key when Char.to_int 'a' = key -> Some 7
          | key when Char.to_int 'b' = key -> Some 3
          | _ -> None
      )
      in

      let residual = Diff.propagate model formula in

      (* Prints: "Residual formula: ((7 >= 5) ^ (3 < 7))" *)
      printf "Residual formula: %s\n"
        (Formula.to_string residual
          ~key:(fun uid -> Char.to_string (Char.of_int_exn uid)))
    ]}
*)
let propagate (model : 'k Model.t) (formula : (bool, 'k) Formula.t)
  : (bool, 'k) Formula.t =
  let vars = Formula.keys formula in
  let model_unboxed = Model.fold model vars ~init:Int.Map.empty ~f:Map.set
  in
  let rec aux : type a. (a,'k) Formula.t -> (a,'k) Formula.t = fun f ->
    match f with
    | Const_bool _ -> f
    | Const_int _ -> f

    | Not (Binop (Equal, _, _)) -> f
    | Not e ->
      let e' = aux e in
      Not e'

    | And es ->
      let es' = List.map es ~f:aux in
      And es'

    | Binop (Not_equal, _, _) -> f
    | Binop (op, l, r) ->
      let l' = aux l in
      let r' = aux r in
      Binop (op, l', r')

    | Key (I x) ->
      begin match Map.find model_unboxed x with
        | Some v -> Const_int v
        | None -> f
        end
    | _ -> f
  in

  aux formula

