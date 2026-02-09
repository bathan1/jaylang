(* We include this specific implementation of [Formula.LOGIC] 
   since a large number of expressions ceval generates
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

    ...

    This module normalizes all inputs into [<=] relations
    and {b ignores} [<>] relations. So rather than handle
    [<>], [Diff] expects the top-level {!Formula.solver} 
    solver to rewrite inequalities into equivalent 
    disjunctions and call this module on the {i split} cases.
*)
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

    {2 Extracting 2 leqs}

    {[
    let () =
      Diff.extract (And [
        Binop (Less_than_eq, Key a, Key b);
        Binop (Less_than_eq, Key c, Key d);
      ])
      |> fun ls -> printf "Atoms list has size %d\n" (List.length ls)
    ]}

    This would print:

    {["Atoms list has size 2"]}
*)
let rec extract (formula : (bool, 'k) Formula.t) : atom list =
  formula
  |> function
    (* x = c -> (x - 0 <= c) and (0 - y) <= -c *)
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

  (* x > y -> (y - x) <= -1 (difference is at least 1) *)
  | Binop (Greater_than, Key I x, Key I y)
  | Binop (Less_than,    Key I y, Key I x)
  | Not Binop (Greater_than_eq, Key I x, Key I y)
  | Not Binop (Less_than_eq,    Key I y, Key I x) ->
      [{ x = y; y = x; c = -1 }]

  (* x + c <= y  ->  x - y <= -c *)
  | Binop (Less_than_eq, Binop (Plus, Key I x, Const_int c), Key I y)
  | Binop (Less_than_eq, Binop (Plus, Const_int c, Key I x), Key I y) ->
      [{ x; y; c = -c }]

  (* y <= x + c  ->  y - x <= c *)
  | Binop (Less_than_eq, Key I y, Binop (Plus, Key I x, Const_int c))
  | Binop (Less_than_eq, Key I y, Binop (Plus, Const_int c, Key I x)) ->
      [{ x = y; y = x; c }]

  (* x - c <= y  ->  x - y <= c *)
  | Binop (Less_than_eq, Binop (Minus, Key I x, Const_int c), Key I y) ->
      [{ x; y; c }]

  (* y <= x - c  ->  y - x <= -c *)
  | Binop (Less_than_eq, Key I y, Binop (Minus, Key I x, Const_int c)) ->
      [{ x = y; y = x; c = -c }]

  | And exprs ->
    exprs
    |> List.map ~f:extract
    |> List.concat
  | _ ->
    []
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
let check (atoms : atom list) : 'k Solution.t =
  (* collect variables *)
  let vars =
    List.fold atoms ~init:Int.Set.empty ~f:(fun acc {x; y; _} ->
      Set.add (Set.add acc x) y)
  in

  let vars = Set.add vars 0 in  (* sentinel node *)

  let n = Set.length vars in

  (* initialize all distances to 0 *)
  let dist =
    Set.fold vars ~init:Int.Map.empty ~f:(fun m v ->
      Map.set m ~key:v ~data:0)
  in

  (* relax all constraints once *)
  let relax_all dist =
    List.fold atoms ~init:dist ~f:(fun dist {x; y; c} ->
      let dx = Map.find_exn dist x in
      let dy = Map.find_exn dist y in
      let candidate = dy + c in
      if candidate < dx then
        Map.set dist ~key:x ~data:candidate
      else
        dist
    )
  in

  (* run N - 1 relaxation passes *)
  let dist =
    let rec iter i dist =
      if i = 0 then dist
      else
        let dist' = relax_all dist in
        iter (i - 1) dist'
    in
    iter (n - 1) dist
  in

  let violating =
    List.filter atoms ~f:(fun {x; y; c} ->
      let dx = Map.find_exn dist x in
      let dy = Map.find_exn dist y in
      dy + c < dx
    )
  in

  if not (List.is_empty violating) then begin
    Solution.Unsat
  end else
    let keys =
      Map.keys dist |> List.filter ~f:(fun v -> v <> 0)
    in
    Solution.Sat (
      Model.of_local dist
        ~lookup:(fun m k -> Option.map (Map.find m k) ~f:(fun v -> -v))
        ~keys
    )
;;

let extend
  (formula : (bool, 'k) Formula.t)
  (solution_state : 'k Model.t)
  : 'k Model.t
=
  let atoms : atom list =
    extract formula
  in

  match check atoms with
  | Solution.Unsat
  | Solution.Unknown ->
      failwith "Diff.extend: check returned Unsat/Unknown (invariant violated)"

  | Solution.Sat graph ->
      Model.fold graph
        ~init:solution_state
        ~f:(fun acc ~key ~data ->
          let sym = (Utils.Separate.I key) in
          match acc.value sym with
          | Some _ ->
            acc
          | None ->
              {
                value =
                  (fun (type a) (s : (a, 'k) Symbol.t) ->
                     match s with
                     | I k when k = key ->
                         Some (Obj.magic data : a)
                     | _ ->
                         acc.value s
                  );

                keys =
                  key :: acc.keys
              }
        )
