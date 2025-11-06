open Core

type 'a assignment = ('a * bool) list
type 'a var = 'a
type 'a literal = | Pos of 'a var | Neg of 'a var
type 'a clause = 'a literal list
type 'a cnf = 'a clause list

(** Checks if key X is in the list of assignments A and if so, what boolean value_tuple0
    it takes on. If X is not in A, then this returns `None` *)
let rec lookup (equal : 'a -> 'a -> bool) (x : 'a) (a : 'a assignment) : bool option =
  match a with
  | [] -> None
  | (y, v) :: rest -> if equal x y then Some v else lookup equal x rest

(** Evaluates what value LIT would take on with assignments A, if any at all. *)
let eval_literal (equal : 'a -> 'a -> bool) (a : 'a assignment) (lit : 'a literal) : bool option =
  match lit with
  | Pos x -> lookup equal x a
  | Neg x -> Option.map (lookup equal x a) ~f:not

(** Prunes one level of literals in clause C with respect to assignments in A. *)
let simplify_clause (equal : 'a -> 'a -> bool) (a : 'a assignment) (c : 'a clause)
  : [ `Satisfied | `Conflict | `Reduced of 'a clause ] =
  let rec aux acc curr = match curr with
    | [] ->
        if List.is_empty acc then `Conflict else `Reduced (List.rev acc)
    | lit :: rest -> (
        match eval_literal equal a lit with
        | Some true -> `Satisfied
        | Some false -> aux acc rest
        | None -> aux (lit :: acc) rest )
  in
  aux [] c

(** Prunes one level of literals from the clauses in CNF based on assignments in A. *)
let simplify_cnf (equal : 'a -> 'a -> bool) (a : 'a assignment) (cnf : 'a cnf)
  : ('a cnf * bool) =
  let rec aux acc curr = match curr with
    | [] -> (List.rev acc, false)
    | clause :: rest -> (
        match simplify_clause equal a clause with
        | `Satisfied -> aux acc rest
        | `Conflict -> ([], true)
        | `Reduced c -> aux (c :: acc) rest )
  in
  aux [] cnf

let rec unit_propagate (equal : 'a -> 'a -> bool)
                       (a : 'a assignment)
                       (cnf : 'a cnf)
  : ('a assignment * 'a cnf * bool) =
  match List.find cnf ~f:(fun c -> List.length c = 1) with
  | None -> (a, cnf, false)
  | Some [lit] ->
      let (v, value) =
        match lit with
        | Pos x -> (x, true)
        | Neg x -> (x, false)
      in
      let a' = (v, value) :: a in
      let cnf', conflict = simplify_cnf equal a' cnf in
      if conflict then (a', cnf', true)
      else unit_propagate equal a' cnf'
  | _ -> (a, cnf, false)

let rec dpll (equal : 'a -> 'a -> bool)
             (a : 'a assignment)
             (cnf : 'a cnf)
  : 'a assignment option =
  let a, cnf, conflict = unit_propagate equal a cnf in
  if conflict || List.exists cnf ~f:List.is_empty then None
  else if List.is_empty cnf then Some a
  else
    let vars =
      cnf |> List.concat
          |> List.filter_map ~f:(function Pos x | Neg x -> Some x)
          |> List.dedup_and_sort ~compare:Poly.compare
    in
    let unassigned =
      List.find vars ~f:(fun v -> Option.is_none (lookup equal v a))
    in
    match unassigned with
    | None -> Some a
    | Some v ->
        let try_value value =
          let a' = (v, value) :: a in
          let cnf', conflict = simplify_cnf equal a' cnf in
          if conflict then None else dpll equal a' cnf'
        in
        match try_value true with
        | Some sol -> Some sol
        | None -> try_value false

