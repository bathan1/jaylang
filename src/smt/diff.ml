(* We include this specific implementation of [Formula.LOGIC] since
   a large number of expressions the cevaluator generates
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
    But we normalize [Formula] inputs into [<=] relations. *)
type atom = {
  (** Variable (id) to subtract. *)
  x : int;

  (** Variable (id) that subtracts [x]. *)
  y : int;

  (** Intepreted as an int {i literal} *)
  c : int;
};;

(** variable -> (tightest) upper bound *)
type 'k solution =
  | Sat of 'k Model.t
  | Unsat

(** Transforms FORMULA into atoms if FORMULA is an [Formula.And].
    Otherwise, it returns an empty list.

    From each [And] list element, we handle exactly 3 binary operations:
    {ol
        {-[<=]}
        {-[=]}
        {-[>=]}
    }
    For {i each} binary operator, we just need to handle 2 relations:
    {ol
        {- [Key, Key] }
        {- [Key, Const_int] (The reverse is also handled under the same match) }
    }

    That's {b 6} total cases to handle:
    {ol
        {- x ≤ y becomes x − y ≤ 0 }
        {- x ≤ c becomes x − 0 ≤ c }
        {- x = y becomes the {b pair} x − y ≤ 0, y − x ≤ 0 }
        {- x = c becomes the {b pair} x − 0 ≤ c, 0 − x ≤ −c }
        {- x ≥ y becomes y − x ≤ 0 }
        {- x ≥ c becomes 0 − x ≤ −c }
    }
    Any other [Formula] type is ignored. *)
let extract (formula : (bool, 'k) Formula.t) : atom list =
  formula
  |> function
  | Formula.And exprs ->
    exprs
    |> List.map ~f:(
      function
      | Formula.Not Formula.Binop (Greater_than, Key (I x), Key (I y))
      | Formula.Binop (Less_than_eq, Key (I x), Key (I y)) ->
        [{ x; y; c = 0 }]

      | Formula.Not Formula.Binop (Greater_than, Key (I x), Const_int c)
      | Formula.Binop (Less_than_eq, Key (I x), Const_int c)
      | Formula.Binop (Greater_than, Const_int c, Key (I x)) ->
        [{ x; y = 0; c }]

      | Formula.Binop (Equal, Key (I x), Key (I y)) ->
        [ { x; y; c = 0 };
          { x = y; y = x; c = 0 } ]

      | Formula.Binop (Equal, Key (I x), Const_int c)
        | Formula.Binop (Equal, Const_int c, Key (I x)) ->
        [ { x; y = 0; c; };
          {x = 0; y = x; c = -c } ]

      | Formula.Not Formula.Binop (Less_than, Key (I x), Key (I y))
      | Formula.Binop (Greater_than_eq, Key (I x), Key (I y)) ->
        [ { x = y; y = x; c = 0 } ]

      | Formula.Not Formula.Binop (Less_than, (Key I x), Const_int c)
      | Formula.Binop (Greater_than_eq, Key (I x), Const_int c)
      | Formula.Binop (Greater_than_eq, Const_int c, Key (I x)) ->
        [ {x = 0; y = x; c = -c}  ]

      | _ -> [])
    |> List.concat
  | _ -> []
;;

let to_global_model (dist : int Int.Map.t) : 'k Model.t =
  {
    Model.value =
      (fun (type a) (sym : (a,'k) Symbol.t) ->
        match sym with
        | I x ->
          Option.map (Map.find dist x) ~f:(fun v ->
            (Obj.magic v : a)
          )
        | B _ ->
          None
      )
  };;

(** Search for the tightest upper bounds of each unique [x, y] variable in ATOMS.
    This is {i decidable}, so it only returns SAT or UNSAT (no unknown cases). *)
let solve (atoms : atom list) : 'k solution =
  let vars =
    List.fold atoms ~init:Int.Set.empty ~f:(fun acc {x; y; _} ->
      Set.add (Set.add acc x) y)
  in
  let edges =
    List.fold atoms ~init:Int.Map.empty ~f:(fun m {x; y; c} ->
      let lst = Map.find m y |> Option.value ~default:[] in
      Map.set m ~key:y ~data:((x, c) :: lst))
  in
  let dist =
    Set.fold vars ~init:Int.Map.empty ~f:(fun m v ->
      let inf = Int.max_value / 4 in
      let initial = if v = 0 then 0 else inf in
      Map.set m ~key:v ~data:initial)
  in
  let in_queue =
    Set.fold vars ~init:(Int.Table.create ()) ~f:(fun tbl v ->
      Hashtbl.set tbl ~key:v ~data:false; tbl)
  in
  let relax =
    Set.fold vars ~init:(Int.Table.create ()) ~f:(fun tbl v ->
      Hashtbl.set tbl ~key:v ~data:0; tbl)
  in
  let q = Queue.create () in
  Set.iter vars ~f:(fun v ->
    Queue.enqueue q v;
    Hashtbl.set in_queue ~key:v ~data:true
  );
  let rec loop dist =
    if Queue.is_empty q then
      Sat (
        Model.of_local dist ~lookup:(
          fun loc key _is_bool -> Map.find loc key
        )
      )
    else begin
      let u = Queue.dequeue_exn q in
      Hashtbl.set in_queue ~key:u ~data:false;

      let dist_u = Map.find_exn dist u in
      let outgoing = Map.find edges u |> Option.value ~default:[] in

      let process_edge (dist, found_cycle) (v, w) =
        let dist_v = Map.find_exn dist v in
        let candidate = dist_u + w in
        if candidate < dist_v then begin
          let dist = Map.set dist ~key:v ~data:candidate in
          let cnt = (Hashtbl.find_exn relax v) + 1 in
          if cnt > Set.length vars then
            (dist, true)
          else begin
            Hashtbl.set relax ~key:v ~data:cnt;
            if not (Hashtbl.find_exn in_queue v) then begin
              Queue.enqueue q v;
              Hashtbl.set in_queue ~key:v ~data:true
              end;
            (dist, false)
            end
          end else
          (dist, found_cycle)
      in

      let (dist', cycle_found) =
        List.fold outgoing ~init:(dist, false) ~f:process_edge
      in

      if cycle_found then Unsat
      else loop dist'
      end
  in

  loop dist
;;

(** Propagate MODEL into FORMULA to spit out a new residual [Formula]. *)
let propagate (model : 'k Model.t) (formula : (bool, 'k) Formula.t)
  : (bool, 'k) Formula.t =
  let vars = Formula.keys formula in
  let model_unboxed = Model.fold model vars 
    ~init:(Int.Map.empty) 
    ~f:(fun acc key data -> Map.set acc ~key ~data)
  in
  let rec aux : type a. (a,'k) Formula.t -> (a,'k) Formula.t = fun f ->
    match f with
    | Const_bool _ -> f
    | Const_int _ -> f

    | Not e ->
      let e' = aux e in
      Not e'

    | And es ->
      let es' = List.map es ~f:aux in
      And es'

    | Binop (op, l, r) ->
      let l' = aux l in
      let r' = aux r in
      Binop (op, l', r')

    | Key (I x) ->
      begin match Map.find model_unboxed x with
        | Some v -> Const_int v
        | None -> f
        end
    | _ -> f
  in

  aux formula

