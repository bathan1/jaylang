open Core

(** PARENT x RANK *)
type t = int array * int array

(** Initialize union find state of N nodes.
    {3 Example}
    {[
      open Core
      open Utils.Uf
      let () =
        let parent, rank = make 3 in
        Array.iteri parent ~f:(fun i x -> (
          printf "(%d) is its own parent: %d\n" i x
        ));
        printf "\n";
        Array.iteri rank ~f:(fun i x -> (
          printf "(%d) starts with rank (%d)\n" i x
        ));

        (* Prints:
            (0) is its own parent: 0
            (1) is its own parent: 1
            (2) is its own parent: 2

            (0) starts with rank (0)
            (1) starts with rank (0)
            (2) starts with rank (0)
        *)
    ]}
*)
let make (n : int) : t =
  (* all disjoint at start *)
  let parent = n |> Array.init ~f:(fun i -> i) in
  (* ranks begin at 0 *)
  let rank = n |> Array.init ~f:(fun _ -> 0) in
  (parent, rank)

(** Find X's parent node given parent array in T.

    Does the path compression heuristic by setting each recursive [parent.(X)] where
    [parent.(X) <> X] to the found root.

    {3 Example}
    {[
      open Core
      open Utils.Uf
      let () =
        let uf = make 3 in
        let was_0_1_disjoint = union uf 0 1 in
        printf "Were (x=0) and (y=1) disjoint? %s\n" (if was_0_1_disjoint then "YUP" else "nah");
        let p0 = find uf 0 in
        let p1 = find uf 1 in
        let is_0_1_connected = (p0 = p1) in
        printf "Is 0 and 1 connected? %s\n" (if is_0_1_connected then "YUP" else "nuh uh");

        (* Prints:
            Were (x=0) and (y=1) disjoint? YUP
            Is 0 and 1 connected? YUP
        *)
    ]}
*)
let rec find (uf : t) (x : int) : int =
  let parent, _rank = uf in
  if x <> parent.(x) then
    let px = find uf parent.(x) in
      parent.(x) <- px;
    px
  else
    parent.(x)

(** Union X with Y based on parents and rank state in T if necessary.
    Returns true if X and Y were disjoint. Otherwise, they already were in
    the same equivalence class.

    {3 Example}
    {[
      open Core
      open Utils.Uf
      let () =
        let uf = make 3 in
        let was_0_1_disjoint = union uf 0 1 in
        printf "Were (x=0) and (y=1) disjoint? %s\n" (if was_0_1_disjoint then "YUP" else "nah");
        let was_0_1_disjoint_again = union uf 0 1 in
        printf "Are (x=0) and (y=1) disjoint after unioning them? %s\n" (if was_0_1_disjoint_again then "YUP" else "nah");

        (* Prints:
            Were (x=0) and (y=1) disjoint? YUP
            Are (x=0) and (y=1) disjoint after unioning them? nah
        *)
    ]}
*)
let union (uf : t) (x : int) (y : int) : bool =
  let parent, rank = uf in
  let rx, ry = find uf x, find uf y in
  if rx = ry then
    false
  else
    match rank.(rx) - rank.(ry) with
    | x when x < 0 ->
      parent.(rx) <- ry;
      true
    | x when x > 0 ->
      parent.(ry) <- rx;
      true
    | _ ->
      parent.(ry) <- parent.(rx);
      rank.(rx) <- rank.(rx) + 1;
      true

