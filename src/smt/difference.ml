(* We include this specific implementation of [Formula.LOGIC] 
   since a large number of expressions ceval generates
   can be simplified / solved using Integer Difference Logic. *)
open Core

type var =
  | Symbol_key of int
  | Z0

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
  x : var;

  (** Variable (id) that subtracts [x]. *)
  y : var;

  (** Intepreted as an int {i literal} *)
  c : int;
}

let rec linearize : type k.
  (int, k) Formula.t -> (int * int) option =
  function
  | Key (I x) ->
      Some (x, 0)

  | Binop (Plus, t, Const_int c) ->
      Option.map (linearize t) ~f:(fun (x, k) ->
        (x, k + c)
      )

  | Binop (Plus, Const_int c, t) ->
      Option.map (linearize t) ~f:(fun (x, k) ->
        (x, k + c)
      )

  | Binop (Minus, t, Const_int c) ->
      Option.map (linearize t) ~f:(fun (x, k) ->
        (x, k - c)
      )

  | _ ->
      None

let rec rewrite_int : type k.
  (int, k) Formula.t -> (int, k) Formula.t =
function
  | Binop (Plus, a, b) ->
      Binop (Plus, rewrite_int a, rewrite_int b)

  | Binop (Minus, a, b) ->
      Binop (Minus, rewrite_int a, rewrite_int b)

  | t ->
      t

let rec rewrite : type k.
  (bool, k) Formula.t -> (bool, k) Formula.t =
function
  | Binop (Less_than_eq, Const_int c1, rhs) ->
    rewrite (Binop (Greater_than_eq, rhs, Const_int c1))
  | Binop (Less_than, Const_int c1, rhs) ->
      rewrite (Binop (Greater_than, rhs, Const_int c1))
  | Binop (Greater_than_eq, Const_int c1, rhs) ->
      rewrite (Binop (Less_than_eq, rhs, Const_int c1))
  | Binop (Greater_than, Const_int c1, rhs) ->
      rewrite (Binop (Less_than, rhs, Const_int c1))

  | Not (Binop (Less_than, a, b)) ->
      rewrite (Binop (Greater_than_eq, a, b))
  | Not (Binop (Less_than_eq, a, b)) ->
      rewrite (Binop (Greater_than, a, b))
  | Not (Binop (Greater_than, a, b)) ->
      rewrite (Binop (Less_than_eq, a, b))
  | Not (Binop (Greater_than_eq, a, b)) ->
      rewrite (Binop (Less_than, a, b))
  | Binop ((Less_than | Less_than_eq
           | Greater_than | Greater_than_eq) as op,
           lhs,
           Const_int c2) ->
      let lhs = rewrite_int lhs in
      begin
        match linearize lhs with
        | Some (x, k') ->
            Binop (op,
                   Key (I x),
                   Const_int (c2 - k'))
        | None ->
            Binop (op, lhs, Const_int c2)
      end
  | And xs -> And (List.map xs ~f:rewrite)
  | f -> f

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
    [ { x = Symbol_key x; y = Z0; c; };
      {x = Z0; y = Symbol_key x; c = -c } ]

    (* x = y -> (x - y) <= 0 and (y - x) <= 0*)
  | Binop (Equal, Key I x, Key I y) ->
    [ { x = Symbol_key x; y = Symbol_key y; c = 0 };
      { x = Symbol_key y; y = Symbol_key x; c = 0 } ]

    (* x <= y -> (x - y <= 0)
        y >= x -> (x - y <= 0)
        not (x > y) -> x <= y -> (x - y) <= 0 *)
  | Binop (Less_than_eq, Key I x, Key I y)
  | Binop (Greater_than_eq, Key I y, Key I x)
  | Not Binop (Less_than, Key I y, Key I x)
  | Not Binop (Greater_than, Key I x, Key I y) ->
    [{ x = Symbol_key x; y = Symbol_key y; c = 0 }]

    (* x <= c -> (x - 0) <= c
        c >= x -> (x - 0) <= c
        not (x > c) -> x <= c -> (x - 0) <= c *)
  | Binop (Less_than_eq, Key I x, Const_int c)
  | Binop (Greater_than_eq, Const_int c, Key I x)
  | Not Binop (Less_than, Const_int c, Key I x)
  | Not Binop (Greater_than, Key I x, Const_int c) ->
    [{ x = Symbol_key x; y = Z0; c }]

    (* x < c -> x - 0 <= c - 1 *)
  | Binop (Less_than, Key I x, Const_int c)
  | Binop (Greater_than, Const_int c, Key I x)
  | Not Binop (Less_than_eq, Const_int c, Key I x)
  | Not Binop (Greater_than_eq, Key I x, Const_int c) ->
    [{ x = Symbol_key x; y = Z0; c = c - 1 }]

    (* x >= c -> 0 - x <= -c
       not (x < c) -> x >= c -> (0 - x) <= -c *)
  | Binop (Greater_than_eq, Key I x, Const_int c)
  | Binop (Less_than_eq, Const_int c, Key I x)
  | Not Binop (Greater_than, Const_int c, Key I x)
  | Not Binop (Less_than, Key I x, Const_int c) ->
    [ {x = Z0; y = Symbol_key x; c = -c}  ]

  (* x > c -> (0 - x) <= -(c + 1) *)
  | Binop (Greater_than, Key I x, Const_int c)
  | Binop (Less_than, Const_int c, Key I x)
  | Not Binop (Greater_than_eq, Const_int c, Key I x)
  | Not Binop (Less_than_eq, Key I x, Const_int c) ->
    [{ x = Z0; y = Symbol_key x; c = -(c + 1) }]

  (* x > y -> (y - x) <= -1 (difference is at least 1) *)
  | Binop (Greater_than, Key I x, Key I y)
  | Binop (Less_than,    Key I y, Key I x)
  | Not Binop (Less_than_eq,    Key I y, Key I x) ->
      [{ x = Symbol_key y; y = Symbol_key x; c = -1 }]

  | Not Binop (Greater_than_eq, Key I x, Key I y) ->
    [{ x = Symbol_key x; y = Symbol_key y; c = -1 }]

  (* x + c <= y  ->  x - y <= -c *)
  | Binop (Less_than_eq, Binop (Plus, Key I x, Const_int c), Key I y)
  | Binop (Less_than_eq, Binop (Plus, Const_int c, Key I x), Key I y) ->
      [{ x = Symbol_key x; y = Symbol_key y; c = -c }]

  (* y <= x + c  ->  y - x <= c *)
  | Binop (Less_than_eq, Key I y, Binop (Plus, Key I x, Const_int c))
  | Binop (Less_than_eq, Key I y, Binop (Plus, Const_int c, Key I x)) ->
      [{ x = Symbol_key y; y = Symbol_key x; c }]

  (* x - c <= y  ->  x - y <= c *)
  | Binop (Less_than_eq, Binop (Minus, Key I x, Const_int c), Key I y) ->
      [{ x = Symbol_key x; y = Symbol_key y; c }]

  (* y <= x - c  ->  y - x <= -c *)
  | Binop (Less_than_eq, Key I y, Binop (Minus, Key I x, Const_int c)) ->
      [{ x = Symbol_key y; y = Symbol_key x; c = -c }]

  | And exprs ->
    exprs
    |> List.map ~f:extract
    |> List.concat
  | _ ->
    []
;;

let bellman_ford (vertices : int array) (edges : (int * int * int) array) ~(src : int) =
  let n = Array.length vertices in
  let distance, predecessor = Array.foldi
    vertices 
    ~init:(
      Array.init n ~f:(fun i -> if i = src then Some 0 else None),
      Array.init n ~f:(fun _ : int option -> None)
    )
    ~f:(fun i (distance, predecessor) _ -> 
      if i = n - 1 then (distance, predecessor)
      else begin
      let next_distance, next_predecessor = Array.fold 
        edges
        ~init:(distance, predecessor)
        ~f:(fun (distance, predecessor) (u, v, w) -> (
          match (distance.(u), distance.(v)) with
          | None, _ -> (distance, predecessor)
          | Some min_dist_to_u, None -> (* initial case *) begin
              distance.(v) <- Some (min_dist_to_u + w);
              predecessor.(v) <- Some min_dist_to_u;
              distance, predecessor
            end
          | Some min_dist_to_u, Some min_dist_to_v -> begin
            if min_dist_to_u + w < min_dist_to_v then
              distance.(v) <- Some (min_dist_to_u + w);
              predecessor.(v) <- Some u;
            distance, predecessor
            end
        ))
      in
      next_distance, next_predecessor
    end)
  in
  (* detect negative cycle and print it *)
  let cycle_start =
    Array.fold edges ~init:None ~f:(fun acc (u, v, w) ->
      match acc with
      | Some _ -> acc
      | None ->
          match (predecessor.(v), predecessor.(u)) with
          | _, _ ->
            begin 
              match distance.(u), distance.(v) with 
              | None, _ (* then either u or v is not connected to the graph *)
              | _, None -> None
              | Some du, Some dv ->
                if du + w < dv then
                  Some v
                else
                  None
            end
    )
  in
  match cycle_start with
  | None -> `No_negative_cycle (distance, predecessor)
  | Some v ->
      let rec move_back x i =
        if i = 0 then x
        else match predecessor.(x) with
          | None -> x
          | Some parent -> move_back parent (i - 1)
      in
      let cycle_vertex = move_back v n in

      let rec collect_cycle curr acc =
        if List.mem acc curr ~equal:Int.equal then
          curr :: acc
        else
          match predecessor.(curr) with
          | None -> (curr :: acc)
          | Some parent -> collect_cycle parent (curr :: acc)
      in

      let cycle = collect_cycle cycle_vertex [] in
      `Negative_cycle cycle

      (* printf "Negative cycle detected:\n"; *)
      (* List.iter cycle ~f:(fun x -> printf "%d -> " x); *)
      (* printf "%d\n" cycle_vertex; *)
      (**)
      (* raise (Invalid_argument "Negative cycle detected") *)

let normalize (atoms : atom list) =
  let vars =
    atoms
    |> List.concat_map ~f:(fun a -> 
      match a.x, a.y with
      | Symbol_key x, Symbol_key y -> [x; y]
      | Symbol_key key, Z0 | Z0, Symbol_key key -> [key]
      | _ -> []
    )
    |> List.dedup_and_sort ~compare:Int.compare
  in
  let key_to_index =
    vars
    |> List.mapi ~f:(fun i v -> (v, i + 1))
    |> Int.Map.of_alist_exn
  in
  let n = 1 + Map.length key_to_index + 1
  (* [0; x; y; z0] *)
  in
  let get_index = Map.find_exn key_to_index in
  let vertices = Array.init n ~f:(fun i -> i) in
  let edges_constraints = List.filter_map atoms ~f:(fun {x; y; c;} -> (
      match x, y with
      | Symbol_key x, Symbol_key y -> Some (get_index x, get_index y, c)
      | Symbol_key x, Z0 -> Some (get_index x, n - 1, c)
      | Z0, Symbol_key y -> Some (n - 1, get_index y, c)
      | _ -> None
    ))
  in
  let dummy_root_edges =
    List.init n ~f:(fun i -> (0, i, 0))
  in
  vertices, Array.of_list (edges_constraints @ dummy_root_edges), key_to_index

let rec contains_mul_or_div : type s k.
  (s, k) Formula.t -> bool =
  function
  | Binop (Modulus, _, _)
  | Binop (Times, _, _)
  | Binop (Divide, _, _) ->
      true

  | Binop (_, a, b) ->
      contains_mul_or_div a || contains_mul_or_div b

  | Not f ->
      contains_mul_or_div f

  | And xs ->
      List.exists xs ~f:contains_mul_or_div

  | _ ->
      false

(** Search for the tightest upper bounds of each unique [x, y] variable in ATOMS.
    This is {i decidable}, so it only returns SAT or UNSAT (no unknown cases).

    x < 0


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
let check (formula : (bool, 'k) Formula.t) : 'k Solution.t =
  if contains_mul_or_div formula then
    Solution.Unknown
  else
    formula
    |> rewrite
    |> extract
    |> normalize
    |> fun (vertices, edges, key_to_index) ->
      match bellman_ford vertices edges ~src:0 with
      | `Negative_cycle _ ->
          Solution.Unsat
      | `No_negative_cycle (distances, _) ->
          let distances_unwrapped = Array.filter_opt distances in
          let n = Array.length vertices in
          let offset = distances_unwrapped.(n - 1) in
          let keys = Map.keys key_to_index in
          Solution.Sat (
            Model.of_local
              distances_unwrapped
              ~keys
              ~lookup:(fun dist symbol_key ->
                match Map.find key_to_index symbol_key with
                | None -> None
                | Some i ->
                    Some (-1 * (dist.(i) - offset))
              )
          )
;;

let extend
  (formula : (bool, 'k) Formula.t)
  (solution_state : 'k Model.t)
  : 'k Model.t
=
  match check formula with
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

