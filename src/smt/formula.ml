
open Core

module type S = sig
  type ('a, 'k) t

  val equal : ('a, 'k) t -> ('a, 'k) t -> bool

  val const_int : int -> (int, 'k) t
  val const_bool : bool -> (bool, 'k) t

  val symbol : ('a, 'k) Symbol.t -> ('a, 'k) t

  val not_ : (bool, 'k) t -> (bool, 'k) t

  val binop : ('a * 'a * 'b) Binop.t -> ('a, 'k) t -> ('a, 'k) t -> ('b, 'k) t

  val is_const : ('a, 'k) t -> bool

  val and_ : (bool, 'k) t list -> (bool, 'k) t
end

module type SOLVABLE = sig
  include S

  val solve : (bool, 'k) t list -> 'k Solution.t
end

type (_, 'k) t =
  | Const_int : int -> (int, 'k) t
  | Const_bool : bool -> (bool, 'k) t
  | Key : ('a, 'k) Symbol.t -> ('a, 'k) t
  | Not : (bool, 'k) t -> (bool, 'k) t
  | And : (bool, 'k) t list -> (bool, 'k) t
  | Binop : ('a * 'a * 'b) Binop.t * ('a, 'k) t * ('a, 'k) t -> ('b, 'k) t

(* Polymorphic equality is good enough here because keys just use ints
  underneath. I would only write structural equality anyways. *)
let equal a b = 
  Core.phys_equal a b
  || Core.Poly.equal a b

let const_int i = Const_int i
let const_bool b = Const_bool b
let symbol s = Key s

let true_ = Const_bool true
let false_ = Const_bool false

let is_const (type a) (x : (a, 'k) t) : bool =
  match x with
  | Const_int _ | Const_bool _ -> true
  | Key _ | Not _ | And _ | Binop _ -> false

let rec binop : type a b. (a * a * b) Binop.t -> (a, 'k) t -> (a, 'k) t -> (b, 'k) t = fun op x y ->
  match op with
  | Or -> begin
      match x, y with
      | Const_bool true, _ -> Const_bool true
      | _, Const_bool true -> Const_bool true
      | Const_bool false, e -> e
      | e, Const_bool false -> e
      | e1, e2 -> Binop (Or, e1, e2)
    end
  | Equal -> begin
      match x, y with
      | Const_bool true, Key k -> Key k
      | Key k, Const_bool true -> Key k
      | Const_bool false, Key k -> Not (Key k)
      | Key k, Const_bool false -> Not (Key k)
      | Key k1, Key k2 when Symbol.equal k1 k2 -> Const_bool true
      | Const_bool b1, Const_bool b2 -> Const_bool (Bool.equal b1 b2)
      | Const_int i1, Const_int i2 -> Const_bool (i1 = i2)
      | e1, e2 -> Binop (Equal, e1, e2)
    end
  | Not_equal -> not_ (binop Equal x y)
  | Plus -> begin
      match x, y with
      | e, Const_int 0
      | Const_int 0, e -> e
      | Const_int i1, Const_int i2 -> Const_int (i1 + i2)
      | e1, e2 -> Binop (Plus, e1, e2)
    end
  | Minus -> begin
      match x, y with
      | e, Const_int 0 -> e
      | Const_int i1, Const_int i2 -> Const_int (i1 - i2)
      | e1, e2 -> Binop (Minus, e1, e2)
    end
  | Times -> begin
      match x, y with
      | e, Const_int 1
      | Const_int 1, e -> e
      | Const_int i1, Const_int i2 -> Const_int (i1 * i2)
      | e1, e2 -> Binop (Times, e1, e2)
    end
  | Divide -> begin
      match x, y with
      | e, Const_int 1 -> e
      | Const_int i1, Const_int i2 -> Const_int (i1 / i2)
      | e1, e2 -> Binop (Divide, e1, e2)
    end
  | Modulus -> begin
      match x, y with
      | Const_int i1, Const_int i2 -> Const_int (i1 mod i2)
      | e1, e2 -> Binop (Modulus, e1, e2)
    end
  | Less_than -> begin
      match x, y with
      | Const_int i1, Const_int i2 -> Const_bool (i1 < i2)
      | e1, e2 -> Binop (Less_than, e1, e2)
    end
  | Less_than_eq -> begin
      match x, y with
      | Const_int i1, Const_int i2 -> Const_bool (i1 <= i2)
      | e1, e2 -> Binop (Less_than_eq, e1, e2)
    end
  | Greater_than -> begin
      match x, y with
      | Const_int i1, Const_int i2 -> Const_bool (i1 > i2)
      | e1, e2 -> Binop (Greater_than, e1, e2)
    end
  | Greater_than_eq -> begin
      match x, y with
      | Const_int i1, Const_int i2 -> Const_bool (i1 >= i2)
      | e1, e2 -> Binop (Greater_than_eq, e1, e2)
  end

and not_ (e : (bool, 'k) t) : (bool, 'k) t =
  match e with
  | Const_bool b -> Const_bool (not b)
  | Not e' -> e'
  | Binop (Or, e1, e2) -> and_ [ not_ e1 ; not_ e2 ] (* it's easier in general to work with "and" *)
  | _ -> Not e

and and_ (e_ls : (bool, 'k) t list) : (bool, 'k) t =
  match e_ls with
  | [] -> true_ (* vacuous truth *)
  | [ e ] -> e
  | hd :: tl ->
    match hd with
    | Const_bool true -> and_ tl
    | Const_bool false -> false_
    | And e_ls' -> and_ (e_ls' @ tl)
    | e -> 
      match and_ tl with
      | Const_bool false -> false_
      | Const_bool true -> e
      | And tl_exprs when List.exists tl_exprs ~f:(equal (not_ e)) -> false_
      | And tl_exprs when List.exists tl_exprs ~f:(equal e) -> And tl_exprs
      | And tl_exprs -> And (e :: tl_exprs)
      | other when equal other (not_ e) -> false_
      | other when equal other e -> e
      | other -> And [ e ; other ]

module Make_transformer (X : S) = struct
  let rec transform : type a. (a, 'k) t -> (a, 'k) X.t = fun e ->
    match e with
    | Const_int i -> X.const_int i
    | Const_bool b -> X.const_bool b
    | Key s -> X.symbol s
    | Not e' -> X.not_ (transform e')
    | And e_ls -> X.and_ (List.map e_ls ~f:transform)
    | Binop (op, e1, e2) -> X.binop op (transform e1) (transform e2)
end

type 'k solver = (bool, 'k) t list -> 'k Solution.t

type lia_cst_t = {
  (** Encodes a linear integer arithmetic constraint for an integer symbol x
      in range \[LOWER, UPPER), where:
      - LOWER bound is {i inclusive} 
      - UPPER bound is {i exclusive}. *)

  (** List of ints that the symbol explicitly cannot be equal to. *)
  neq : int list;
  (** Inclusive lower bound. *)
  lower : int option;
  (** Exclusive upper bound. *)
  upper : int option;
}

let empty_lia_cst : lia_cst_t = {
  neq = [];
  lower = None;
  upper = None;
}

module IntMap = Map.Make (Int)

let rec next :
  type k.
  lia_cst_t IntMap.t ->
  (bool, k) t ->
  lia_cst_t IntMap.t
  = fun acc el ->
  match el with
  | Binop (op, Const_int v, Key (I x)) ->
    let curr =
      match Map.find acc x with
      | Some bounds -> bounds
      | None -> empty_lia_cst
    in
    let cst =
      match op with
      | Equal -> { curr with lower = Some v; upper = Some (v + 1) }
      | Not_equal -> { curr with neq = v :: curr.neq }
      | Greater_than -> { curr with lower = Some (v + 1) }
      | Greater_than_eq -> { curr with lower = Some v }
      | Less_than -> { curr with upper = Some v }
      | Less_than_eq -> { curr with upper = Some (v + 1) }
    in
    Map.add_exn acc ~key:x ~data:cst
  | Binop (op, Key (I x), Const_int v) ->
    let curr =
      match Map.find acc x with
      | Some bounds -> bounds
      | None -> empty_lia_cst
    in
    let cst =
      match op with
      | Equal -> { curr with lower = Some v; upper = Some (v + 1) }
      | Not_equal -> { curr with neq = v :: curr.neq }
      | Greater_than -> { curr with lower = Some (v + 1) }
      | Greater_than_eq -> { curr with lower = Some v }
      | Less_than -> { curr with upper = Some v }
      | Less_than_eq -> { curr with upper = Some (v + 1) }
    in
    Map.add_exn acc ~key:x ~data:cst
  | Binop (_, Key (I x), Key (I y)) ->
    let acc =
      if Map.mem acc x then acc else Map.add_exn acc ~key:x ~data:empty_lia_cst
    in
    if Map.mem acc y then acc else Map.add_exn acc ~key:y ~data:empty_lia_cst

  | Key key ->
    let x = Utils.Separate.extract key in
    if Map.mem acc x then acc else Map.add_exn acc ~key:x ~data:empty_lia_cst

  | And ls ->
    List.fold ls ~f:next ~init:acc

  | _ -> acc
;;

let decide_eq :
  type k.
  (bool, k) t ->
  lia_cst_t ->
  lia_cst_t ->
  (bool, k) t
  = fun expr lcst rcst ->
  match (lcst.lower, lcst.upper, rcst.lower, rcst.upper) with
  | (Some xl, Some xu, Some yl, Some yu) when xl = xu && yl = yu ->
    Const_bool (xl = yl)
  | (Some xl, Some xu, Some yl, Some yu) when xu < yl || yu < xl ->
    Const_bool false
  | (Some xl, Some xu, _, _) when xl = xu && List.mem rcst.neq xl ~equal:Int.equal ->
    Const_bool false
  | (_, _, Some yl, Some yu) when yl = yu && List.mem rcst.neq yl ~equal:Int.equal ->
    Const_bool false
  | _ -> expr;;

let decide_gt :
  type k.
  int ->
  int ->
  lia_cst_t ->
  lia_cst_t ->
  (bool, k) t
  = fun x y xcst ycst ->
  match xcst.lower, xcst.upper, ycst.lower, ycst.upper with
  | Some xl, _, _, Some yu when xl >= yu ->
    Const_bool true
  | _, Some xu, Some yl, _ when xu <= yl ->
    Const_bool false
  | (Some xl, Some xu, Some yl, Some yu)
    when xu <= yl || yu <= xl ->
    Const_bool (xl > yu)
  | (Some xl, Some xu, None, None)
    when xu - xl = 1 ->
    Binop (Less_than_eq, Key (I y), Const_int xl)
  | (None, None, Some yl, Some yu)
    when yu - yl = 1 ->
    Binop (Greater_than, Key (I x), Const_int yl)
  | _ -> Binop (Greater_than, Key (I x), Key (I y))

let decide (type k) (x, x_cst : int * lia_cst_t) (y, y_cst : int * lia_cst_t) ~(op : Binop.iib Binop.t) ~(fallback : (bool, k) t) = 
  (match op with
    | Equal -> decide_eq fallback x_cst y_cst
    | Not_equal -> 
      begin match decide_eq fallback x_cst y_cst with
      | Const_bool v -> Const_bool (not v)
      | _ -> fallback
      end
    | Less_than_eq
      | Greater_than -> decide_gt x y x_cst y_cst
    | Greater_than_eq
      | Less_than -> decide_gt y x y_cst x_cst)

let rec sub :
  type k.
  lia_cst_t IntMap.t ->
  (bool, k) t ->
  (bool, k) t option
  = fun acc expr ->
  match expr with
  | Binop (_, Key (I _), Const_int _)
    | Binop (_, Const_int _, Key (I _)) -> None
  | Binop (op, Key (I x), Key (I y)) ->
    (x, y)
    |> fun (x, y) -> (Map.find_exn acc x, Map.find_exn acc y)
    |> fun (x_cst, y_cst) -> ((x, x_cst), (y, y_cst))
    |> fun (xc, yc) -> Some (decide xc yc ~op ~fallback:expr)
  | And rest ->
    rest
    |> List.filter_map ~f:(sub acc)
    |> (function 
      | ls when List.exists ls ~f:(function Const_bool false -> true | _ -> false)
        -> Some (Const_bool false)
      | ls -> ls
        |> List.filter ~f:(function Const_bool true -> false | _ -> true)
        |> (function
          | [] -> Some (Const_bool true)
          | [single] -> Some single
          | ls -> Some (And ls)))
  | _ -> Some expr
;;

(** *)
let simplify
  : type k.
  (bool, k) t list ->
  lia_cst_t IntMap.t * (bool, k) t list
  = fun exprs ->
  exprs
  |> List.fold ~f:next ~init:(IntMap.empty : lia_cst_t IntMap.t)
  |> fun tbl ->
  List.filter_map ~f:(fun el -> sub tbl el) exprs
  |> fun red -> (tbl, red)
;;

module Make_solver (X : SOLVABLE) = struct
  module M = Make_transformer (X)

  let solve (exprs : (bool, 'k) t list) : 'k Solution.t =
    exprs
    |> and_
    |> fun red -> simplify [red]
    |> fun (_amap, red) -> List.hd_exn red
    |> function
      | Const_bool false -> Solution.Unsat
      | Const_bool true -> Sat Model.empty
      | e -> X.solve [ M.transform e ]
end

