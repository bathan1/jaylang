open Core

(** A generic map type of symbols FROM namespace ['k] TO assignments of type ['a]. *)
type 'k t = {
  (** Lookup the value of SYMBOL, if Some exists. *)
  value : 'a. ('a, 'k) Symbol.t -> 'a option;
}

(** Lookup calls will just return [None] *)
let empty : 'k t = { value = (fun _ -> None) }

(** Combine partial models LEFT and RIGHT using the "most recent model" 
    strategy (RIGHT is most recent). *)
let merge (left : 'k t) (right : 'k t) : 'k t =
  {
    value =
      (fun (type a) (symbol : (a, 'k) Symbol.t) ->
        match right.value symbol with Some v -> Some v | None -> left.value symbol);
  }

(** Pretty-print SYMBOLS in MODEL. If no assignments are present, returns ["{}"].

    Otherwise, it formats each [symbol] [value] pair using the string returned by
    PP_ASSIGNMENT, separating by SEP which is ["\n"] by default:

    {
    <pp_assignment s1 v1>
    <pp_assignment s2 v2>
    ...
    } 
*)
let to_string
    (type a k)
    ?(sep = "\n")
    (model : k t)
    (symbols : (a, k) Symbol.t list)
    ~(pp_assignment : (a, k) Symbol.t -> a -> string)
  : string
=
  let assignments =
    symbols
    |> List.filter_map ~f:(fun sym ->
         match model.value sym with
         | Some v -> Some (pp_assignment sym v)
         | None -> None)
  in

  match assignments with
  | [] ->
      "{}"

  | _ ->
      let body =
        String.concat ~sep assignments
      in
      Printf.sprintf "{%s%s%s}" sep body sep

