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

(** Splits [(bool, 'k) t] FORMULA into 2 cases that are each
    {i potentially} satisfiable. Split functions are what make
    {b non-convex} theories usable by the solver.
*)
type 'k split_fn = (bool, 'k) t -> ((bool, 'k) t * (bool, 'k) t) option

(** Encapsulates {i subsets} of theories for simple
    expressions. Based on Logics from {{:https://smt-lib.org/logics-all.shtml} SMT-LIB}.
    These will generally be {b convex} theories that don't result in a case split.
    That's what {!SPLIT} is for. *)
module type LOGIC = sig
  (** Whatever type the logic works with. *)
  type atom

  (** Transform FORMULA into a list of atoms to pass into [solve]. *)
  val extract : (bool, 'k) t -> atom list

  (** Search for a satisfying model of ATOMS, if some exists. *)
  val solve : atom list -> 'k Solution.t
end


(** An adapter type for calling an SMT solver backend.

    You can bind a [LOGIC] list of modules to LOGICS in order
    to preprocess (and hopefully outright solve) future
    calls to SOLVE [[ t ]].

    For example, {!Overlays.Typed_z3} can be used as an argument to {!Make_solver}:
{[
module Backend_z3 = Formula.Make_solver(Typed_z3)
let result = Backend_z3.solve [
  And [
    Binop (Equal, Key a, Const_int 123456);
    Binop (Equal, Key b, Const_int 123456);
    Binop (Equal, Key c, Const_int 123456);
    Binop (Equal, Key d, Const_int 123456);
  ];
]
]}
*)
module type SOLVABLE = sig
  include S

  (** List of case splitters that the solver should
      branch exprs on when it needs to make a decision. *)
  val splits : 'k split_fn list

  (** List of logics the solver should process prior to
      calling the backend solve.

      For example, to preprocess with IDL reasoning using the
      [Diff] module:
      {[
      module MySolvable = struct
        include Overlays.Typed_z3
        let logics : (module Formula.LOGIC) list = [
          (module Diff)
        ]
      end
      ]}
  *)
  val logics : (module LOGIC) list

  (** Searches for a satisfying model of the {i conjunction} of EXPRS.

      Example:
      {[
      let expr = And [
        Binop (Equal, Key a, Const_int 123456);
        Not (Binop (Equal, Key b, Const_int 123456));
        Binop (Equal, Key c, Const_int 123456);
        Binop (Equal, Key d, Const_int 123456);
      ]
      let result = MySolvable.solve [expr]
      ]}
  *)
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

(** Pretty prints FORMULA, with optional KEY function.

    Key function is passed the [uid] of the Key and is asked to
    turn that into a meaningful string.

    For example, if [uid]s were encoded as ASCII codes for keys 'a', 'b', 'c', 'd',
    we could decode that to a [string]:
    {[
      printf "(%d) Hybrid solve on: %s\n"
        i
        (
          Formula.to_string expr ~key:(
            fun uid -> (
              uid
              |> Char.of_int_exn
              |> Char.to_string
            )
        ));
    ]}
    The log would look something like:
    {[
    Hybrid solve on: ((a = 123456) ^ (b = 123456) ^ (not (c = 123456)) ^ (d = 123456))
    ]}
*)
let rec to_string : type a k. ?key:(int -> string) -> (a, k) t -> string =
  fun
    ?(key=fun uid -> (
    sprintf "<Key#%d>" uid
  )) formula ->
  match formula with
  | Const_int i -> Int.to_string i
  | Const_bool b -> Bool.to_string b
  | Key (I uid)
    | Key (B uid) -> key uid
  | Not e ->
    sprintf "(not %s)" (to_string e ~key)
  | And es ->
    let parts = List.map es ~f:(to_string ~key) in
    sprintf "(%s)" (String.concat ~sep:" ^ " parts)
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
    sprintf "(%s %s %s)" (to_string e1 ~key) op_str (to_string e2 ~key)

(** Evaluate constant literals from FORMULA. *)
let rec evaluate : type a k. (a, k) t -> (a, k) t = function
  | Const_int _ as e -> e
  | Const_bool _ as e -> e
  | Key _ as e -> e

  | Not e ->
    let e' = evaluate e in
    not_ e'

  | And es ->
    es
    |> List.map ~f:evaluate
    |> and_

  | Binop (op, e1, e2) ->
    let e1' = evaluate e1 in
    let e2' = evaluate e2 in
    binop op e1' e2'

(** Get the uids of all the keys in FORMULA.

    For example:
    {[
      let propagate (model : 'k Model.t) (formula : (bool, 'k) Formula.t)
        : (bool, 'k) Formula.t =
        let vars = Formula.keys formula in
    ]}
*)
let keys (formula : (bool, 'k) t) : int list =
  let rec go :
    type a. int list -> (a, 'k) t -> int list =
    fun acc f ->
    match f with
    | Const_bool _ | Const_int _ -> acc

    | Key (I uid)
      | Key (B uid) ->
      uid :: acc

    | Not e ->
      go acc e

    | And es ->
      List.fold es ~init:acc ~f:(fun acc e -> go acc e)
    | Binop (_, l, r) ->
      let acc = go acc l in
      go acc r
  in
  go [] formula

open Utils
let partition (and_expr : (bool, 'k) t) : (bool, 'k) t =
  let exprs = (match and_expr with
    | And ls -> ls
    | _ -> []) in
  if List.is_empty exprs then
    and_expr
  else
    let symbols = keys and_expr in
    let sorted = Stdlib.List.sort_uniq Int.compare symbols in
    let index_to_symbol = Array.of_list sorted in
    let n = Array.length index_to_symbol in
    let symbol_to_index = Hashtbl.of_alist_exn (module Int) (
      List.of_array (
        Array.mapi index_to_symbol ~f:(fun i uid -> uid, i)
      )
    ) in
    let union_in_atom uf atom =
      match atom with
      | Binop (_, Key (I x), Key (I y)) ->
        let ix = Hashtbl.find_exn symbol_to_index x in
        let iy = Hashtbl.find_exn symbol_to_index y in
        ignore (Uf.union uf ix iy)
      | _ -> ()
    in
    let uf = Uf.make n in
    List.iter exprs ~f:(fun f -> union_in_atom uf f);
    let buckets = Array.init n ~f:(fun _ -> ref []) in

    let rec keys_of_atom acc = function
      | Binop (_, Key (I x), Key (I y)) -> x :: y :: acc
      | Binop (_, Key (I x), _) -> x :: acc
      | Binop (_, _, Key (I y)) -> y :: acc
      | Not e -> keys_of_atom acc e
      | And es -> List.fold es ~init:acc ~f:keys_of_atom
      | _ -> acc
    in

    List.iter exprs ~f:(fun atom ->
      match keys_of_atom [] atom with
      | [] -> ()
      | uid :: _ ->
        let idx = Hashtbl.find_exn symbol_to_index uid in
        let root = Uf.find uf idx in
        buckets.(root) := atom :: !(buckets.(root))
    );

    let components = Array.fold buckets ~init:[] ~f:(fun acc atoms_ref ->
      match !(atoms_ref) with
      | [] -> acc
      | atoms ->
        (* Reverse to retain left-to-right ordering in EXPR *)
        (And (List.rev atoms)) :: acc
    ) in

    And (List.rev components)
;;

let bools (formula : (bool, 'k) t) : Int.Set.t Int.Map.t =
  let get_set map key =
    match Map.find map key with
    | Some ls -> ls
    | _ -> Int.Set.empty
  in
  formula
  |> function
  | And ls -> (
    List.fold ls ~init:(Int.Map.empty : Int.Set.t Int.Map.t) ~f:(fun acc f -> (
      match f with
      | Binop (Not_equal, Key I x, Const_int c)
        | Binop (Not_equal, Const_int c, Key I x)
        | Not (Binop (Equal, Key I x, Const_int c))
        | Not (Binop (Equal, Const_int c, Key I x)) ->
        let set = get_set acc x in
        let next = Set.add set c in
        Map.set acc ~key:x ~data:next
      | _ -> acc
    ))
  )
  | _ -> Int.Map.empty
;;

(** Maybe branch on an unresolved literal in [(bool, 'k) t] of CONJUNCTIONS 
    ({!And}) based on the rules encoded in the [(module SPLIT) list] SPLITS, 
    if such a branch exists.

    If it does exist, then this returns a 3 tuple
    RESULT where:
      - [RESULT[0] = left split]
      - [RESULT[1] = right split]
      - [RESULT[2] = expression with the literal removed.]
    And RESULT is just the very {b first} split function that returns [Some] result.
*)
let branch
  (splits : 'k split_fn list)
  (conjunction : (bool, 'k) t)
  : ((bool, 'k) t * (bool, 'k) t * (bool, 'k) t) option =
  match conjunction with
  | And exprs ->
    let rec aux acc = function
      | [] -> None
      | x :: xs ->
        let rest = And (List.rev_append acc xs) in
        let rec try_splitters = function
          | [] ->
            aux (x :: acc) xs
          | split :: ss ->
            match split x with
            | Some (left, right) ->
              Some (left, right, rest)
            | None ->
              try_splitters ss
        in
        try_splitters splits
    in
    aux [] exprs
  | _ -> None

module Make_solver (X : SOLVABLE) = struct
  module M = Make_transformer (X)

  (** Search for a [Smt.Solution solution] that satisfies the 
      {i conjunction} of [bool, 'k) t list] EXPRS for [int]
      TRIES_LEFT more recursive calls at most, which by 
      default is set to 100 arbitrarily.

      We assume calling [X.solve] is expensive because it's 
      external, so this attempts to reduce EXPRS to a [Const_bool] 
      using user-defined OCaml modules at first.

      So we take that tradeoff of extra computation overhead with 
      the hopes of {i hitting} a solution more often than {i missing} one.

      If it can't reduce into a [Const_bool], then it calls [X.solve] on [EXPRS].

      ...

      This is essentially a dumbed down version of the DPLL(T) algorithm.
  *)
  let rec solve ?(tries_left = 100) (exprs : (bool, 'k) t list) : 'k Solution.t =
    if tries_left <= 0 then
      Solution.Unknown
    else
      exprs
      |> and_
      |> function
      | Const_bool true -> Solution.Sat Model.empty
      | Const_bool false -> Solution.Unsat
      | e ->
        if List.is_empty X.logics then
          X.solve [M.transform e]
        else
          let theory_unsat =
            List.exists X.logics ~f:(fun (module L) ->
              match L.solve (L.extract e) with
              | Unsat -> true
              | _ -> false
            )
          in
          if theory_unsat then
            Solution.Unsat
          else
            match branch X.splits e with
            | None ->
              let model =
                List.fold X.logics
                  ~init:Model.empty
                  ~f:(fun acc_model (module L) ->
                    match L.solve (L.extract e) with
                    | Sat m -> Model.merge acc_model m
                    | _ -> acc_model
                  )
              in
              Solution.Sat model

            | Some (left, right, rest) ->
              let left_branch =
                match rest with
                | And xs -> And (left :: xs)
                | _ -> And [left; rest]
              in

              let right_branch =
                match rest with
                | And xs -> And (right :: xs)
                | _ -> And [right; rest]
              in

              begin
                match solve [left_branch] with
                | Solution.Sat m ->
                  Solution.Sat m

                | Solution.Unsat ->
                  solve [right_branch]

                | Solution.Unknown ->
                  X.solve [M.transform e]
                end
end

