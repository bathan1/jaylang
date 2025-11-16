type 'k t = { value : 'a. ('a, 'k) Symbol.t -> 'a option }

let empty : 'k t = { value = (fun _ -> None) }

(** Combine partial models M1 and M2 using the "most recent model" strategy (M2
    is most recent). *)
let merge (m1 : 'k t) (m2 : 'k t) : 'k t =
  {
    value =
      (fun (type a) (sym : (a, 'k) Symbol.t) ->
        match m2.value sym with Some v -> Some v | None -> m1.value sym);
  }

(** Closes F in the return function so that F is called on the
    assignment found in MODEL if it exists. Returns empty string otherwise. *)
let to_string (type a k) (model : k t) ~(f : (a, k) Symbol.t -> a -> string) : (a, k) Symbol.t -> string =
  fun (symbol : (a, k) Symbol.t) -> (
    symbol
    |> model.value
    |> function
      | Some assignment -> f symbol assignment
      | None -> ""
  )
