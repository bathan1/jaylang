
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

type (_, 'k) t =
    | Const_int : int -> (int, 'k) t
    | Const_bool : bool -> (bool, 'k) t
    | Key : ('a, 'k) Symbol.t -> ('a, 'k) t
    | Not : (bool, 'k) t -> (bool, 'k) t
    | And : (bool, 'k) t list -> (bool, 'k) t
    | Binop : ('a * 'a * 'b) Binop.t * ('a, 'k) t * ('a, 'k) t -> ('b, 'k) t

module type LOGIC = sig
    type atom
    type 'k solution =
        | Sat of 'k Model.t
        | Unsat

    (** Transform FORMULA into atoms list. *)
    val extract : (bool, 'k) t -> atom list

    (** Search for a satisfying model of ATOMS, if some exists. *)
    val solve : atom list -> 'k solution

    val propagate : 'k Model.t -> (bool, 'k) t -> (bool, 'k) t
end


module type SOLVABLE = sig
    include S
    val logics : (module LOGIC) list

    val solve : (bool, 'k) t list -> 'k Solution.t
end

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

let decide (type k) (x : int) (y : int) ~(op : Binop.iib Binop.t) ~(csts : lia_cst_t IntMap.t) : (bool, k) t = 
    (x, y)
    |> fun (x, y) -> (Map.find_exn csts x, Map.find_exn csts y)
    |> fun (x_cst, y_cst) ->
    (let fallback op =
        (Binop (op, Key (I x), Key (I y)))
        in match op with
        | Equal -> decide_eq (fallback Equal) x_cst y_cst
        | Not_equal -> 
            begin match decide_eq (fallback Not_equal) x_cst y_cst with
                | Const_bool v -> Const_bool (not v)
                | _ -> (fallback Not_equal)
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

    (* [Binops] between [Key]s and [Const_int]s are recorded in ACC,
     so they can be implicitly reduced to a `true`

     ... meaning it can be pruned to a [None]. *)
    | Binop (_, Key (I _), Const_int _)
        | Binop (_, Const_int _, Key (I _)) -> None

    (* Resolve new expression between a binop between 2 int [Key]s 
     from caller's DECIDE *)
    | Binop (op, Key (I x), Key (I y)) -> Some (decide x y ~op ~csts:acc)
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
    (* if it's not an [And] then return expr immediately *)
    | _ -> Some expr
;;

(** [[simplify EXPR]] is a 2 tuple [(CONSTRAINTS, REDUCTION)] where:

    - CONSTRAINTS is a map from [Symbol] to [lia_cst_t].
    and
    - REDUCTION is the unit propagation [(bool, k) t] of EXPR, if there is anything to propagate.

    If EXPR is unabled to be propagated (i.e is a {i conjunction}), then REDUCTION
    is just a copy of EXPR. *)
let simplify (type k) (expr: (bool, k) t) :
    lia_cst_t IntMap.t * (bool, k) t
    = 
    let get_constraints = fun (exprs : (bool, k) t list) ->
        exprs |> List.fold ~f:next ~init:(IntMap.empty : lia_cst_t IntMap.t)
    in
    let reduce (exprs : (bool, k) t list) (csts : lia_cst_t IntMap.t) =
        csts,
        And (List.filter_map ~f:(fun el -> sub csts el) exprs)
    in
    match expr with
    | Binop (Equal, Key (I x), Const_int v) -> (
        IntMap.of_alist_exn [
            (x, { empty_lia_cst with lower = Some v; upper = Some (v + 1); })
        ],
        Const_bool true
    )
    | And exprs ->
        exprs 
        |> get_constraints
        |> reduce exprs
    | _ -> (IntMap.empty, expr)
;;

let model_of_lia (type k) (assignments : lia_cst_t IntMap.t) : k Model.t =
    let value : type a. (a, k) Symbol.t -> a option =
        function
        | I x -> Some (
            x
            |> Map.find_exn assignments
            |> fun cst -> Option.value_exn cst.lower
            |> fun v -> v + 1
        )
        | _ -> None
    in
    { value }
;;

let rec to_string : type a k. (a, k) t -> string = fun expr ->
    match expr with
    | Const_int i -> Int.to_string i
    | Const_bool b -> Bool.to_string b
    | Key s ->
        (match s with
            | I uid ->
                Printf.sprintf "%c" (Char.of_int_exn uid)
            | B uid ->
                Printf.sprintf "%c" (Char.of_int_exn uid))

    | Not e ->
        Printf.sprintf "(not %s)" (to_string e)
    | And es ->
        let parts = List.map es ~f:to_string in
        Printf.sprintf "(%s)" (String.concat ~sep:" ^ " parts)
    | Binop (op, e1, e2) ->
        let op_str =
            match op with
            | Equal -> "="
            | Not_equal -> "!="
            | Less_than -> "<"
            | Less_than_eq -> "<="
            | Greater_than -> ">"
            | Greater_than_eq -> ">="
            | Plus -> "+"
            | Minus -> "-"
            | Times -> "*"
            | Divide -> "/"
            | Modulus -> "mod"
            | Or -> "or"
        in
        Printf.sprintf "(%s %s %s)" (to_string e1) op_str (to_string e2)


module Make_solver (X : SOLVABLE) = struct
    module M = Make_transformer (X)

    (** Search for a [Smt.Solution solution] that satisfies the {i conjunction} of EXPRS.

    We assume calling [X.solve] is expensive, so this attempts to reduce EXPRS to a [Const_bool].

    If it can't reduce into a [Const_bool], then it calls [X.solve] on the {i reduced conjunction}. *)
    let solve (exprs : (bool, 'k) t list) : 'k Solution.t =
        exprs
        |> and_
        |> function
        | Const_bool true -> Solution.Sat Model.empty
        | Const_bool false -> Solution.Unsat
        | e ->
            printf "initial expr = %s\n" (to_string e);
            let (partial_model, simplified) =
                List.fold X.logics
                    ~init:(Model.empty, e)
                    ~f:(fun (acc_model, acc_formula) (module L) ->
                        let atoms = L.extract acc_formula in
                        match L.solve atoms with
                        | L.Unsat ->
                            (acc_model, Const_bool false)

                        | L.Sat m ->
                            let acc_model' = Model.merge acc_model m in
                            let residual = L.propagate m acc_formula in
                            (acc_model', residual)
                    )
            in
            printf "simplified: %s\n" (to_string simplified);
            match simplified with
            | Const_bool false -> Solution.Unsat
            | Const_bool true  -> Solution.Sat partial_model
            | e'' ->
                (* backend solver *)
                let backend_solution = X.solve [ M.transform e'' ] in
                match backend_solution with
                | Solution.Sat backend_model ->
                    Solution.Sat (Model.merge partial_model backend_model)
                | other -> other
end

