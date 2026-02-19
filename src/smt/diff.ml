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
  | None -> (distance, predecessor)
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

      printf "Negative cycle detected:\n";
      List.iter cycle ~f:(fun x -> printf "%d -> " x);
      printf "%d\n" cycle_vertex;

      raise (Invalid_argument "Negative cycle detected")

let normalize atoms =
  List.iter atoms ~f:(fun {x; y; c} -> (
    printf "{ x = %d; y = %d; c = %d }\n" x y c
  ));
  let vars =
    atoms
    |> List.concat_map ~f:(fun a -> [a.x; a.y])
    |> List.filter ~f:(fun v -> v <> 0)
    |> List.dedup_and_sort ~compare:Int.compare
  in

  let mapping =
    vars
    |> List.mapi ~f:(fun i v -> (v, i + 1))
    |> Int.Map.of_alist_exn
  in

  let map_var v =
    if v = 0 then 0
    else Map.find_exn mapping v
  in

  let atoms' =
    List.map atoms ~f:(fun a ->
      { x = map_var a.x;
        y = map_var a.y;
        c = a.c })
  in
  let n = Map.length mapping in
  let vertices = Array.init n ~f:(fun i -> i) in
  let edges = (
    atoms'
    |> List.map ~f:(fun {x; y; c;} -> (x, y, c))
    |> List.to_array
  )
  in
  vertices, edges, mapping

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
let check (_formula : atom list) : 'k Solution.t =
  Solution.Sat Model.empty
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

