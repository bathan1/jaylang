def bellman_ford(vertices: list[int], edges: list[tuple[int, int, int]], src: int):
    n = len(vertices)
    distance: list[int | None] = [None for _ in range(n)]
    predecessor: list[int | None] = [None for _ in range(n)]
    distance[src] = 0

    for _ in range(n - 1):
        for src, dst, weight in edges:
            dist_to_src = distance[src]
            if dist_to_src is None:
                continue
            dist_to_dst = distance[dst]
            if dist_to_dst is None or dist_to_src + weight < dist_to_dst:
                distance[dst] = dist_to_src + weight
                predecessor[dst] = src

    for u, v, weight in edges:
        dist_u = distance[u]
        dist_v = distance[v]
        if dist_u is None:
            continue
        if dist_v is None:
            continue
        if dist_u + weight < dist_v:
            x = v
            for _ in range(n):
                x = predecessor[x]
            if x is None:
                print("Unexpected None predecessor")
                break

            # Step 2: build cycle
            cycle = []
            cur: int | None = x
            while True:
                cycle.append(cur)
                if (cur := predecessor[cur]) is None or cur == x:
                    break

            cycle.reverse()
            raise AssertionError("Graph contains a negative cycle", cycle)

    return distance, predecessor
