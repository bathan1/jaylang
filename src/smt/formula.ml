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

    {2 Splitting on Disequalities (aka. {!Splits.lucky_guess})}
    {[
    let lucky_guess : 'k Formula.split_fn = function
      | Not (Binop (Equal, Key I l, Const_int r))
        | Not (Binop (Equal, Const_int r, Key I l))
        | Binop (Not_equal, Key I l, Const_int r)
        | Binop (Not_equal, Const_int r, Key I l) ->
        Some (
          Binop (Less_than, Key (I l), Const_int r),
          Binop (Greater_than, Key (I l), Const_int r)
        )
      | _ -> None
    ]}
*)
type 'k split_fn = (bool, 'k) t -> ((bool, 'k) t * (bool, 'k) t) option

(** Specific logic that checks FORMULA for a SOLUTION. *)
type 'k check_fn = (bool, 'k) t -> 'k Solution.t

(** Adapter type for calling an SMT solver backend.

    You can bind a [LOGIC] list of modules to LOGICS along with 
    branch functions ({!split_fn}) to SPLITS in order
    to preprocess (and hopefully outright solve) future
    calls to SOLVE [[ t ]].

    {2 {!Overlays.Typed_z3} as an argument to {!Make_solver}}
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
      branch exprs on when it needs to make a decision.

      {2 Including the {!Splits.lucky_guess} branch function}
      {[
      module MySolveable = struct
        include Overlays.Typed_z3
        let splits = [Splits.lucky_guess]
      end
      ]}
  *)
  val splits : 'k split_fn list

  (** List of logics the solver should process prior to
      calling the backend solve.

      {2 Including the {!Diff} module}
      {[
      module MySolvable = struct
        include Overlays.Typed_z3
        let logics : (module Formula.LOGIC) list = [
          (module Diff)
        ]
      end
      ]}
  *)
  val checks : 'k check_fn list

  (** Searches for a satisfying model of the {i conjunction} of EXPRS.

      {3 Example}
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

let to_string (type a) ~(uid_to_string : int -> string) (x : (a, 'k) t) : string =
  let rec to_string : type a. (a, 'k) t -> string = function
    | Const_int i -> string_of_int i
    | Const_bool b -> string_of_bool b
    | Key I k | Key B k -> uid_to_string k
    | Not e -> Format.sprintf "(not %s)" (to_string e)
    | And e_ls -> List.fold e_ls ~init:"" ~f:(fun acc e ->
        if String.is_empty acc then to_string e else acc ^ " ^ " ^ to_string e
      )
    | Binop (bop, e1, e2) ->
      Format.sprintf "(%s %s %s)" (to_string @@ Obj.magic e1) (Binop.to_string bop) (to_string @@ Obj.magic e2)
  in
  to_string x

(* Polymorphic equality is good enough here because keys just use ints
  underneath. I would only write structural equality anyways. *)
(* let equal a b = *)
(*   Core.phys_equal a b *)
(*   || Core.Poly.equal a b *)
let rec equal : type a. (a, 'k) t -> (a, 'k) t -> bool = fun x y ->
  phys_equal x y || poly_equal x y
and poly_equal : type a b. (a, 'k) t -> (b, 'k) t -> bool = fun x y ->
  match x, y with
  | Const_int i, Const_int j -> i = j
  | Const_bool b, Const_bool c -> Bool.equal b c
  | Key I k, Key I k' -> k = k'
  | Key B k, Key B k' -> k = k'
  | Not e, Not e' -> equal e e'
  | And l, And l' -> List.equal equal l l'
  | Binop (b, l, r), Binop (b', l', r') ->
    Binop.poly_equal b b'
    && poly_equal l l'
    && poly_equal r r'
  | _ -> false

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

let rec eval_int (f : (int, 'k) t) : int =
  match f with
  | Const_int i -> i

  | Binop (Plus, a, b) ->
      eval_int a + eval_int b

  | Binop (Minus, a, b) ->
      eval_int a - eval_int b

  | Binop (Times, a, b) ->
      eval_int a * eval_int b

  | _ ->
      failwith "Expected fully substituted integer expression!"


let rec rewrite_int : type k.
  (int, k) t -> (int, k) t =
  function
  | Binop (Plus, a, b) ->
    Binop (Plus, rewrite_int a, rewrite_int b)

  | Binop (Minus, a, b) ->
    Binop (Minus, rewrite_int a, rewrite_int b)

  | t ->
    t

let rec linearize : type k.
  (int, k) t -> (int * int) option =
  function
  | Key (I x) ->
    Some (x, 0)

  | Binop (Plus, t, Const_int c) ->
    Option.map (linearize t) ~f:(fun (x, k) ->
      (x, k + c)
    )

  | Binop (Plus, Const_int c, t) ->
    Option.map (linearize t) ~f:(fun (x, k) ->
      (x, k + c)
    )

  | Binop (Minus, t, Const_int c) ->
    Option.map (linearize t) ~f:(fun (x, k) ->
      (x, k - c)
    )

  | _ ->
    None

type int_bound = {
  lower : int option;
  upper : int option;
  nots : int list;
}

let update_bounds x f bounds_state =
  let existing =
    List.Assoc.find bounds_state x ~equal:Int.equal
    |> Option.value ~default:{ lower=None; upper=None; nots=[] }
  in
  let updated = f existing in
  (x, updated)
  :: List.Assoc.remove bounds_state x ~equal:Int.equal

let append_neq x val_neq bounds_state =
  let existing =
    List.Assoc.find bounds_state x ~equal:Int.equal
    |> Option.value ~default:{ lower = None; upper = None; nots = [] }
  in

  let within_bounds =
    let lower_ok =
      match existing.lower with
      | None -> true
      | Some l -> val_neq >= l
    in
    let upper_ok =
      match existing.upper with
      | None -> true
      | Some u -> val_neq <= u
    in
    lower_ok && upper_ok
  in

  let appended =
    if not within_bounds then
      existing
    else
      { existing with
        nots =
          if List.mem existing.nots val_neq ~equal:Int.equal
          then existing.nots
          else val_neq :: existing.nots
      }
  in

  (x, appended)
  :: List.Assoc.remove bounds_state x ~equal:Int.equal

let is_unsat { lower; upper; _ } =
  match lower, upper with
  | Some l, Some u -> l > u
  | _ -> false

let violates_nots { lower; upper; nots } =
  match lower, upper with
  | Some l, Some u when l = u ->
      List.mem nots l ~equal:Int.equal
  | _ -> false

let constraints_for_var x { lower; upper; nots } =
  let base =
    []
    |> (fun acc ->
      match lower with
      | Some l -> Binop (Greater_than_eq, Key (I x), Const_int l) :: acc
      | None -> acc)
    |> (fun acc ->
      match upper with
      | Some u -> Binop (Less_than_eq, Key (I x), Const_int u) :: acc
      | None -> acc)
  in

  let nots_formula =
    List.map nots ~f:(fun n ->
      Not (Binop (Equal, Key (I x), Const_int n)))
  in

  base @ nots_formula

let rebuild bounds_state rest =
  bounds_state
  |> List.concat_map ~f:(fun (x, b) ->
       constraints_for_var x b)
  |> function
     | [] -> And (rest)
     | [f] -> And (f :: rest) 
     | xs -> And (xs @ rest)

let count_neqs : type k. (bool, k) t -> int = fun formula ->
  let rec count (acc : int) (formula : (bool, k) t) =
    match formula with
    | Not (Binop (Equal, _, _)) | Binop (Not_equal, _, _) -> acc + 1
    | And formulas -> List.fold formulas ~init:acc ~f:count
    | _ -> acc
  in
  count 0 formula

(** *)
let rewrite : type k.
  (bool, k) t -> (bool, k) t * int = fun formula ->
  let rest_formulas : (bool, k) t list = [] in
  let rec loop_over 
    (bounds_state : (int * int_bound) list) 
    (rest : (bool, k) t list)
    =
    function
    | Not (Binop (Equal, Const_int c, Key (I x)))
    | Not (Binop (Equal, Key (I x), Const_int c))
    | Binop (Not_equal, Const_int c, Key (I x))
    | Binop (Not_equal, Key (I x), Const_int c) -> (
        (append_neq x c bounds_state, rest)
      )
    | Binop (Less_than_eq, Const_int c1, rhs) -> 
      loop_over bounds_state rest (Binop (Greater_than_eq, rhs, Const_int c1))
    | Binop (Less_than, Const_int c1, rhs) ->
      loop_over bounds_state rest (Binop (Greater_than, rhs, Const_int c1))
    | Binop (Greater_than_eq, Const_int c1, rhs) ->
      loop_over bounds_state rest (Binop (Less_than_eq, rhs, Const_int c1))
    | Binop (Greater_than, Const_int c1, rhs) ->
      loop_over bounds_state rest (Binop (Less_than, rhs, Const_int c1))

    | Not (Binop (Less_than, a, b)) ->
      loop_over 
        bounds_state
        rest
        (Binop (Greater_than_eq, a, b))
    | Not (Binop (Less_than_eq, a, b)) ->
      loop_over bounds_state rest (Binop (Greater_than, a, b))
    | Not (Binop (Greater_than, a, b)) ->
      loop_over bounds_state rest (Binop (Less_than_eq, a, b))
    | Not (Binop (Greater_than_eq, a, b)) ->
      loop_over bounds_state rest (Binop (Less_than, a, b))
    | Binop ((Less_than | Less_than_eq
      | Greater_than | Greater_than_eq) as op,
      lhs,
      Const_int c2) -> (
      let lhs = rewrite_int lhs in
        match linearize lhs with
        | Some (x, k') ->
          let c = c2 - k' in 
          let bounds_state = (
            match op with
            | Less_than_eq -> (
                update_bounds 
                  x 
                  (fun b -> {
                    b with upper = Some (
                      match b.upper with
                      | None -> c
                      | Some u -> min u c
                    )
                  })
                  bounds_state
              )
            | Less_than -> (
                update_bounds
                  x
                  (fun b -> { 
                    b with upper = Some (
                      match b.upper with
                      | None -> c - 1
                      | Some u -> min u (c - 1)
                    ) 
                  })
                  bounds_state
              )
            | Greater_than_eq -> (
                update_bounds 
                  x 
                  (fun b -> {
                    b with lower = Some (
                      match b.lower with
                      | None -> c
                      | Some l -> max l c
                    )
                  })
                  bounds_state
              )
            | Greater_than -> (
                update_bounds
                  x
                  (fun b -> {
                    b with lower = Some (
                      match b.lower with
                      | None -> c + 1
                      | Some l -> max l (c + 1)
                    )
                  })
                  bounds_state
              )
            | _ -> bounds_state
          ) in (bounds_state, rest)
        | None ->
          (* Should never hit... *)
          (bounds_state, Binop (op, lhs, Const_int c2) :: rest)
      )
    | And xs ->
      List.fold xs ~init:(bounds_state, rest) ~f:(fun (st, rest_acc) f ->
        loop_over st rest_acc f
      )
    | f -> (bounds_state, f :: rest)
  in
  let bounds_state, rest = loop_over [] rest_formulas formula
  in
  match List.find bounds_state ~f:(fun (_, bound) -> is_unsat bound || violates_nots bound) with
  | Some _ -> Const_bool false, 0
  | None -> (
      rebuild bounds_state rest
      |> fun rewritten -> (rewritten, (count_neqs rewritten))
    )

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


(** [branch splits conjunction] separates CONJUNCTION 
    into equivalent left and right expressions if 
    that transformation is encoded by a function from SPLITS. *)
let branch
    (splits : 'k split_fn list)
    (conjunction : (bool, 'k) t)
    : ((bool, 'k) t * (bool, 'k) t ) option =
  let exprs = match conjunction with
    | And xs -> xs
    | e -> [e]
  in
  let rec aux acc = function
    | [] -> None
    | x :: xs ->
      let rest = List.rev_append acc xs in
      let rec try_splitters = function
        | [] -> aux (x :: acc) xs
        | split :: ss ->
          match split x with
          | Some (left, right) ->
            Some (and_ (left :: rest), and_ (right :: rest))
          | None ->
            try_splitters ss
      in
      try_splitters splits
  in
  aux [] exprs

let extract_all_keys : type a k. (a, k) t -> int list =
  let rec aux : type a k. (a, k) t -> int list = function
    | Const_int _ -> []
    | Const_bool _ -> []
    | Key (I sym)
      | Key (B sym) -> [sym]
    | Not t -> aux t
    | And ts -> List.concat_map ts ~f:aux
    | Binop (_, lhs, rhs) -> aux lhs @ aux rhs
  in
  aux
;;

(** [substitute formula model] is FORMULA with assignments from MODEL written in. *)
let rec substitute :
  type a k.
  (a, k) t -> k Model.t -> (a, k) t =
  fun formula model ->
  match formula with
  | Const_bool _
    | Const_int _ ->
    formula

  | Key sym ->
    begin match sym with
      | I _ ->
        begin match model.value sym with
          | Some value -> Const_int value
          | None -> Const_int 0
          end
      | B _ ->
        Const_bool true
      end

  | Binop (op, l, r) ->
    begin match op with
      | Plus | Minus | Times | Divide | Modulus | Not_equal | Or ->
        Binop (op,
          substitute l model,
          substitute r model)

      | Less_than
        | Less_than_eq
        | Greater_than
        | Greater_than_eq
        | Equal ->
        Binop (op,
          substitute l model,
          substitute r model)
      end

  | Not f ->
    Not (substitute f model)

  | And fs ->
    And (List.map fs ~f:(fun f -> substitute f model))

let cTHRESHOLD_NEQ = 6

module Make_solver (X : SOLVABLE) = struct
  module M = Make_transformer (X)

  let is_backend_used = ref false

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

      This is basically a dumbed down version of the DPLL algorithm.
  *)
  let solve (exprs : (bool, 'k) t list) : 'k Solution.t =
    let rec solve_formula (formula : (bool, 'k) t) : 'k Solution.t = 
      match formula with
      | Const_bool false -> 
        Solution.Unsat
      | Const_bool true -> Solution.Sat Model.empty
      | _ ->
        match branch X.splits formula with
        | Some (left, right) ->
          begin match solve_formula left with
            | Solution.Sat _ as sat -> sat
            | Solution.Unsat
            | Solution.Unknown -> solve_formula right
            end
        | None ->
          let formula_keys = extract_all_keys formula in

          let solution =
            List.fold_until
              X.checks
              ~init:(formula_keys, Model.empty)
              ~f:(fun (remaining_keys, merged_model) (check) ->
                match check formula with
                | Unsat ->
                  Stop Solution.Unsat

                | Sat model ->
                  let remaining_keys =
                    List.filter remaining_keys ~f:(fun k ->
                      not (List.mem model.keys k ~equal:Int.equal))
                  in
                  let merged_model =
                    Model.merge merged_model model
                  in
                  Continue (remaining_keys, merged_model)

                | Unknown ->
                  Continue (remaining_keys, merged_model)
              )
              ~finish:(fun (remaining_keys, merged_model) ->
                if List.is_empty remaining_keys then
                  Solution.Sat merged_model
                else
                  Solution.Unknown
              )
          in
          solution
    in
    exprs
    |> and_
    |> rewrite
    |> fun (formula_rewritten, num_neqs) -> (
      match num_neqs with
      | x when x < cTHRESHOLD_NEQ -> solve_formula formula_rewritten
      | _ -> Solution.Unknown
    )
    |> function
      | Solution.Unknown -> 
        is_backend_used := true;
        let result = X.solve [M.transform formula_rewritten] in
        begin match result with
          | Solution.Sat model ->
            Solution.Sat
              { value = model.value
                ; keys = extract_all_keys formula_rewritten
              }
          | _ -> result
          end
      | solution -> solution
end

module Make_solver_raw (X : SOLVABLE) = struct
  module M = Make_transformer (X)

  let solve (exprs : (bool, 'k) t list) : 'k Solution.t =
    match and_ exprs with
    | Const_bool false -> Unsat
    | Const_bool true -> Sat Model.empty
    | e -> X.solve [ M.transform e ]
end

