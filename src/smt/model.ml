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
    value = fun (type a) (symbol : (a, 'k) Symbol.t) -> (
      match right.value symbol with
      | Some v -> Some v
      | None -> left.value symbol
    )
  }

(** Pretty-print SYMBOLS in MODEL. If no assignments are present, returns ["{}"].

    Otherwise, it formats each [symbol] [value] pair using the string returned by
    PP_ASSIGNMENT, separating by SEP which is ["\n"] by default:

    {[
    {
      (pp_assignment s1 v1)
      (pp_assignment s2 v2)
      ...
    }
    ]}
*)
let to_string
    (type a k)
    ?(sep = "\n")
    (model : k t)
    (symbols : (a, k) Symbol.t list)
    ~(pp_assignment : (a, k) Symbol.t -> a -> string)
  : string
=
    symbols
    |> List.filter_map ~f:(fun sym ->
         match model.value sym with
         | Some v -> Some (pp_assignment sym v)
         | None -> None)
    |> function
      | [] -> "{}"
      | assignments ->
          let body =
            String.concat ~sep assignments
          in
          Printf.sprintf "{%s%s%s}" sep body sep

(** Fold VARS over their value from MODEL into
    the type from INIT, with F being the fold function.

    For example, we can fold assignments into an [Int.Map]:

    {[
    let model_unboxed = Model.fold model vars 
      ~init:(Int.Map.empty) 
      ~f:(fun acc key data -> Map.set acc ~key ~data)
    ]}
*)
let fold
  (model : 'k t)
  (vars : int list)
  ~(init: 'a) 
  ~(f : 'a -> int -> int -> 'a) =
    vars
    |> List.fold ~init ~f:(fun acc x ->
      match model.value (I x) with
      | Some v -> f acc x v
      | None -> acc
    )

(** "Cast" LOCAL into type [Model.t] by wrapping [Model.value]
    calls with the LOOKUP callback.

    LOOKUP is passed in arguments LOCAL, the symbol's int id,
    and a bool flag indicating if this is a boolean key or not.

    Example usage from [Diff.solve]:
    {[
      if Queue.is_empty q then
        Sat (
          Model.of_local dist ~lookup:(
            fun loc key _is_bool -> Map.find loc key
          )
        )
    ]}
    *)
let of_local (local : 'a) ~(lookup : 'a -> int -> bool -> 'b option): 'k t =
  {
    value =
      (fun (type a) (sym : (a,'k) Symbol.t) ->
        match sym with
        | I x ->
          Option.map (lookup local x false) ~f:(fun v ->
            (Obj.magic v : a)
          )
        | B x ->
          Option.map (lookup local x true) ~f:(fun v ->
            (Obj.magic v : a)
          )
      )
  }
