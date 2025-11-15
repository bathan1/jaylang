type 'k t = { value : 'a. ('a, 'k) Symbol.t -> 'a option; }

let empty : 'k t = { value = (fun _ -> None); }

(** Combine partial models M1 and M2 using the "most recent model" strategy (M2 is most recent). *)
let merge (m1 : 'k t) (m2 : 'k t) : 'k t =
    { value =
        (fun (type a) (sym : (a, 'k) Symbol.t) ->
            match m2.value sym with
            | Some v -> Some v
            | None -> m1.value sym)
    }

