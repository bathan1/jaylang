open Core

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


let n = 7
let vertices = Array.init n ~f:(fun i -> i)
let edges = [|
  (1, 3, -5); (* x1 <= x3 - 5 *)
  (1, 4, -3); (* x1 <= x4 - 3 *)
  (2, 1, 3); (* x2 <= x1 + 3 *)
  (3, 2, 2); (* x3 <= x2 + 2 *)
  (3, 4, -1); (* x3 <= x4 - 1 *)
  (4, 2, 5); (* x4 <= x2 + 5 *)
|]

let () =
  let distance, _ = bellman_ford vertices edges ~src:0 in
  let distance_ls = List.of_array distance in
  printf "Distances: %s\n" (List.to_string distance_ls ~f:(function
    | None -> "disconnected"
    | Some v -> Int.to_string v
  ));
