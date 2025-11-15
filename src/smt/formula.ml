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
  (** Encapsulates {i specific} subsets of theories for very simple
      expressions. Based on Logics from {{:https://smt-lib.org/logics-all.shtml} SMT-LIB}. *)

  (** Whatever type the logic works with, which can be anything. *)
  type atom

  (** The frontend only works with {b DECIDABLE} logics, 
      so we don't need to handle Unknowns. *)
  type 'k solution =
    | Sat of 'k Model.t
    | Unsat

  (** Transform FORMULA into a list of atoms to pass into [solve]. *)
  val extract : (bool, 'k) t -> atom list

  (** Search for a satisfying model of ATOMS, if some exists. *)
  val solve : atom list -> 'k solution

  (** Rewrite FORMULA based on given MODEL. *)
  val propagate : 'k Model.t -> (bool, 'k) t -> (bool, 'k) t
end

module type SOLVABLE = sig
  (** An 'adapter' for calling a solver backend in plain OCaml. *)
  include S
  (** List of logics the solver should process prior to
      calling the backend solve. *)
  val logics : (module LOGIC) list

  (** Searches for a satisfying model of the {i conjunction} of EXPRS. *)
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

let rec to_string : type a k. (a, k) t -> string = fun expr ->
  match expr with
  | Const_int i -> Int.to_string i
  | Const_bool b -> Bool.to_string b
  | Key s ->
    (match s with
      | I uid ->
        Printf.sprintf "<IntKey#%d>" uid
      | B uid ->
        Printf.sprintf "<BoolKey#%d>" uid)

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
      match simplified with
      | Const_bool false -> Solution.Unsat
      | Const_bool true  -> printf "no shot?\n"; Solution.Sat partial_model
      | e'' ->
        printf "uh %s\n" (to_string e'');
        (* backend solver *)
        let backend_solution = X.solve [ M.transform e'' ] in
        match backend_solution with
        | Solution.Sat backend_model ->
          Solution.Sat (Model.merge partial_model backend_model)
        | other -> other
end

