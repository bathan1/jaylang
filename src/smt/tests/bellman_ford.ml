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
  (* if the graph is fully connected, then this doesn't remove any elements... *)
  let distance = 
    Array.filter_map distance ~f:(function
      | None -> None
      | Some min_distance -> Some min_distance
    )
  in
  Array.fold edges ~init:(distance, predecessor) ~f:(fun (distance, predecessor) (u, v, w) -> (
    if distance.(u) + w < distance.(v) then
      raise (Invalid_argument "Negative cycle detected")
    else
      distance, predecessor
  ))


let n = 5
let vertices = Array.init n ~f:(fun i -> i)
let edges = [|
  (0, 2, -6);
  (0, 3, -3);
  (1, 0, 3);
  (2, 1, 2);
  (2, 3, -1);
  (2, 1, 5);
|]

let () =
  let distance, _ = bellman_ford vertices edges ~src:0 in
  let distance_ls = List.of_array distance in
  printf "Distances: %s\n" (List.to_string distance_ls ~f:Int.to_string);
