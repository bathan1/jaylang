open Core


(** Generic map-like type of symbols FROM namespace ['k] TO assignments
    of type ['a]. *)
type 'k t = {
  (** Lookup the value of SYMBOL, if Some exists. *)
  value : 'a. ('a, 'k) Symbol.t -> 'a option;

  keys : int list;
}

(** Lookup calls will just return [None]. *)
let empty : 'k t = { 
  value = (fun _ -> None);
  keys = [];
}

(** Combine partial models LEFT and RIGHT using the "most recent model"
    strategy (RIGHT is most recent).

    {3 Example}
    {[
    let () =
      let open Symbol in
      let a = AsciiSymbol.make_int 'a'
      and b = AsciiSymbol.make_int 'b'
      and c = AsciiSymbol.make_int 'c'
      in
      let pp_model = Model.to_string ~pp_assignment:(
        fun (I x) v -> sprintf "  %c => %d" (Char.of_int_exn x) v
      ) in
      let left_model = Model.of_local 0 ~lookup:(fun _ uid ->
        uid
        |> function
          | key when Char.to_int 'a' = key -> Some 7
          | key when Char.to_int 'b' = key -> Some 3
          | _ -> None
      ) in
      let right_model = Model.of_local 0 ~lookup:(fun _ uid ->
        uid
        |> function
          | key when Char.to_int 'a' = key ->
            (* This overrides 'a' in left_model *)
            Some (-7)
          | key when Char.to_int 'b' = key -> Some 3
          | key when Char.to_int 'c' = key -> Some 10
          | _ -> None
      ) in
      let merged = Model.merge left_model right_model in
      printf "Merged models: %s\n" (pp_model merged [a; b; c;])
      (*
      *)
    ]}

    Prints:

    {[
    "Merged models: {
      a => -7
      b => 3
      c => 10
    }"
    ]}
*)
let merge (left : 'k t) (right : 'k t) : 'k t =
  {
    keys =
      List.concat [left.keys; right.keys]
      |> List.dedup_and_sort ~compare:Int.compare;
    value =
      fun (type a) (symbol : (a, 'k) Symbol.t) ->
        match right.value symbol with
        | Some v -> Some v
        | None -> left.value symbol
  }


(** Pretty-print SYMBOLS in MODEL. It formats each [symbol] [value] pair using the
    string returned by PP_ASSIGNMENT, separated by SEP (["\n"] by default).

    Otherwise, returns ["{}"].

    {3 Example}
    {[
    let () =
      let open Symbol in
      let a = AsciiSymbol.make_int 'a' and b = AsciiSymbol.make_int 'b'
      in
      let model = Model.of_local 0 ~lookup:(fun _ uid ->
        uid
        |> function
          | key when Char.to_int 'a' = key -> Some 7
          | key when Char.to_int 'b' = key -> Some 3
          | _ -> None
      )
      in
      let str_repr = Model.to_string model [a; b;] ~sep:("; ") ~pp_assignment:(
          fun (I uid) v -> sprintf "  %c => %d" (Char.of_int_exn uid) v
      )
      in
      printf "Model formatted: %s\n" str_repr;
      (*
        
      *)
    ;;
    ]}

    Prints:
    {[
    "Model formatted: { a => 7; b => 3 }"
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

(** Fold KEYS over their value from MODEL by calling [F INIT var data].

    {3 Fold over a trivial static model}
    {[
    let () =
      let open Symbol in
      let a = AsciiSymbol.make_int 'a'
      and b = AsciiSymbol.make_int 'b'
      in
      let get_uid = Utils.Separate.extract in
      let model = Model.of_local ~keys:[a; b;] 0 ~lookup:(fun _ uid ->
        uid
        |> function
          | key when Char.to_int 'a' = key -> Some 7
          | key when Char.to_int 'b' = key -> Some 3
          | _ -> None
      ) in
      Model.fold model ~init:Int.Map.empty ~f:Map.set
      |> Map.to_alist
      |> List.to_string ~f:(fun (k, v) -> sprintf "%c=%d" (Char.of_int_exn k) v)
      |> printf "Folded: %s\n";
    ]}

    Prints:

    {["Folded: (a=7 b=3)"]}
*)
let fold
  (model : 'k t)
  ~(init : 'a)
  ~(f : 'a -> key:int -> data:int -> 'a)
=
  model.keys
  |> List.fold ~init ~f:(fun acc x ->
      match model.value (I x) with
      | Some v -> f acc ~key:x ~data:v
      | None -> acc
    )

(** Cast LOCAL into type {!Model.t} by wrapping [!Model.value]
    calls with the LOOKUP callback.

    LOOKUP is passed in arguments
    {ol
      {- [local]: A reference to passed LOCAL argument. }
      {- [uid]: The [int] uid of the [Symbol] to lookup. }
    }
    It should return an [option] of whatever value LOCAL holds for the
    given [uid].

    {2 From an {!Int.Map} local solution}

    Local solutions that use some kind of a {!Map} map nicely to
    to the 'global' {!t}:

    {[
    let () =
      let int_map = (
        Int.Map.empty
        |> Map.add_exn ~key:(Char.to_int 'a') ~data:0
        |> Map.add_exn ~key:(Char.to_int 'b') ~data:1
      ) in
        let pp_model = Model.to_string ~sep:("; ") ~pp_assignment:(
          fun (I x) v -> sprintf " %c => %s" (Char.of_int_exn x) (
            if v = 0 then "hello" else "world"
          )
        ) in
        let model = Model.of_local int_map ~lookup:Map.find in
        pp_model model [a; b;]
        |> printf "From local: %s\n";
    ]}

    This prints:

    {["From local: { a => hello; b => world }"]}
*)
let of_local (local : 'a) ~(keys : int list) ~(lookup : 'a -> int -> 'b option): 'k t =
  {
    value =
      (fun (type a) (sym : (a,'k) Symbol.t) ->
        match sym with
        | I x ->
          Option.map (lookup local x) ~f:(fun v ->
            (Obj.magic v : a)
          )
        | B x ->
          Option.map (lookup local x) ~f:(fun v ->
            (Obj.magic v : a)
          )
      );
    keys
  }

