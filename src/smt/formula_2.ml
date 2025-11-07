open Smt.Sat

(** Use same type as Smt.Formula.t *)
type ('a, 'k) t = ('a, 'k) Smt.Formula.t

let rec tseitin
    (f : ('a, 'k) t)
    (fresh : unit -> int)
    (cnf_acc : int Smt.Sat.cnf)
    (atom_table : (('a, 'k) t, int) Core.Hashtbl.t)
    : int * int Smt.Sat.cnf =
    match f with
    | Const_bool true ->
        let v = fresh () in
        (v, [ [Pos v] ] @ cnf_acc)

    | Const_bool false ->
        let v = fresh () in
        (v, [ [Neg v] ] @ cnf_acc)

    | Key _ 
        | Binop ((Equal | Less_than | Greater_than
        | Less_than_eq | Greater_than_eq), _, _) ->
        (* atomic proposition — already has an ID *)
        let v = Core.Hashtbl.find_exn atom_table f in
        (v, cnf_acc)

    | Not e ->
        let (v_e, cnf_acc) = tseitin e fresh cnf_acc atom_table in
        let v = fresh () in
        let new_clauses =
            [ [Neg v; Neg v_e];
                [Pos v; Pos v_e] ]
        in
        (v, new_clauses @ cnf_acc)

    | And [e1; e2] ->
        let (v1, cnf1) = tseitin e1 fresh cnf_acc atom_table in
        let (v2, cnf2) = tseitin e2 fresh cnf1 atom_table in
        let v = fresh () in
        let new_clauses =
            [ [Neg v; Pos v1];
                [Neg v; Pos v2];
                [Neg v1; Neg v2; Pos v] ]
        in
        (v, new_clauses @ cnf2)

    | Binop (Or, e1, e2) ->
        let (v1, cnf1) = tseitin e1 fresh cnf_acc atom_table in
        let (v2, cnf2) = tseitin e2 fresh cnf1 atom_table in
        let v = fresh () in
        let new_clauses =
            [ [Neg v1; Pos v];
                [Neg v2; Pos v];
                [Neg v; Pos v1; Pos v2] ]
        in
        (v, new_clauses @ cnf2)

    | And es when List.length es > 2 ->
        let v_list, cnf' =
            Core.List.fold_left es ~init:([], cnf_acc)
                ~f:(fun (acc_vars, acc_cnf) e ->
                    let (v_e, acc_cnf') = tseitin e fresh acc_cnf atom_table in
                    (v_e :: acc_vars, acc_cnf'))
        in
        let v = fresh () in
        let new_clauses =
            (Core.List.map v_list ~f:(fun vi -> [Neg v; Pos vi]))
            @ [ (Core.List.map v_list ~f:(fun vi -> Neg vi)) @ [Pos v] ]
        in
        (v, new_clauses @ cnf')

    | _ ->
        let v = fresh () in
        (v, cnf_acc)

let model_of_pairs
    (pairs : ((bool, 'k) t * bool) list)
    : 'k Smt.Model.t =
    { value =
        (fun (type a) (sym : (a, 'k) Smt.Symbol.t) ->
            match sym with
            | B _ ->
                let maybe_entry =
                    Core.List.find pairs ~f:(fun (atom, _) ->
                        match atom with
                        | Smt.Formula.Key s -> Smt.Symbol.equal s sym
                        | _ -> false)
                in
                (Core.Option.map maybe_entry ~f:snd : a option)
            | I _ ->
                (None : a option))
    }

let equal = Smt.Formula.equal
let const_int = Smt.Formula.const_int
let const_bool = Smt.Formula.const_bool
let symbol = Smt.Formula.symbol
let and_ (type k) (e_ls : (bool, k) t list) : (bool, k) t =
    let pos = Hashtbl.create (1 lsl 16) and neg = Hashtbl.create (1 lsl 16) in
    let stack = ref e_ls in
    let rec loop acc =
        match !stack with
        | [] -> (match acc with
            | [] -> Smt.Formula.Const_bool true
            | [e] -> e
            | _ -> And (List.rev acc))
        | Const_bool false :: _ -> Const_bool false
        | Const_bool true :: tl -> stack := tl; loop acc
        | And xs :: tl          -> stack := xs @ tl; loop acc
        | (Not e as ne) :: tl   ->
            stack := tl;
            if Hashtbl.mem pos e then Const_bool false
            else if Hashtbl.mem neg e then loop acc
            else (Hashtbl.add neg e (); loop (ne :: acc))
        | e :: tl ->
            stack := tl;
            if Hashtbl.mem neg e then Const_bool false
            else if Hashtbl.mem pos e then loop acc
            else (Hashtbl.add pos e(); loop (e :: acc))
    in
    loop []
let rec not_ (e : (bool, 'k) t) : (bool, 'k) t =
    match e with
    | Const_bool b -> Const_bool (not b)
    | Not e' -> e'
    | Binop (Or, e1, e2) -> and_ [not_ e1 ; not_ e2]
    | _ -> Not e

let is_const = Smt.Formula.is_const

let rec binop : type a b. (a * a * b) Smt.Binop.t -> (a, 'k) t -> (a, 'k) t -> (b, 'k) t =
    fun op x y ->
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
        | Key k1, Key k2 when equal k1 k2 -> Const_bool true
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

open Smt.Formula
open Core
open Smt.Sat

let rec to_string : type a k. (a, k) t -> string = function
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

let solve (exprs : (bool, 'k) t list) : 'k Smt.Solution.t =
    let add_bool_binop acc (op : _ Smt.Binop.t) e1 e2 =
        let f' = Binop (op, e1, e2) in
        f' :: acc
    in
    let rec collect_atoms : type a k. (bool, k) t list -> (a, k) t -> (bool, k) t list =
        fun acc f ->
        match f with
        | Const_bool _ | Const_int _ -> acc
        | Key (B _) -> f :: acc
        | Key (I _) -> acc
        | Not e -> collect_atoms acc e
        | And es -> List.fold_left es ~init:acc ~f:collect_atoms
        | Binop (Equal, e1, e2) -> add_bool_binop acc Equal e1 e2
        | Binop (Less_than, e1, e2) -> add_bool_binop acc Less_than e1 e2
        | Binop (Greater_than, e1, e2) -> add_bool_binop acc Greater_than e1 e2
        | Binop (Less_than_eq, e1, e2) -> add_bool_binop acc Less_than_eq e1 e2
        | Binop (Greater_than_eq, e1, e2) -> add_bool_binop acc Greater_than_eq e1 e2
        | Binop (_, e1, e2) ->
            let acc = collect_atoms acc e1 in
            collect_atoms acc e2
    in
    let atoms =
        exprs
        |> List.concat_map ~f:(collect_atoms [])
        |> List.dedup_and_sort ~compare:Poly.compare
    in
    let atom_table = Hashtbl.Poly.create ()
    and id_table = Hashtbl.create (module Int)
    and counter = ref 0 in

    List.iter atoms ~f:(fun atom ->
        Hashtbl.set atom_table ~key:atom ~data:!counter;
        Hashtbl.set id_table ~key:!counter ~data:atom;
        incr counter);

    Printf.printf "Atom table:\n";
    Hashtbl.iteri atom_table ~f:(fun ~key:atom ~data:id ->
        Printf.printf "  %d <-> %s\n" id (to_string atom));
    print_endline "-----\n";

    let fresh () = let v = !counter in incr counter; v in

    let cnf, top_vars =
        List.fold_left exprs ~init:([], []) ~f:(fun (cnf_acc, tops) e ->
            let (v, cnf') = tseitin e fresh cnf_acc atom_table in
            (cnf', v :: tops))
    in

    let top_clauses = [ List.map top_vars ~f:(fun v -> Pos v) ] in
    let cnf = top_clauses @ cnf in

    match dpll equal [] cnf with
    | None -> Smt.Solution.Unsat
    | Some assignment ->
    (* reverse map *)
    let model_pairs =
      List.filter_map assignment ~f:(fun (id, value) ->
        match Hashtbl.find id_table id with
        | Some atom -> Some (atom, value)
        | None -> None)
    in
    if not (Smt.Theory.check model_pairs) then (
      print_endline "Theory conflict — UNSAT.";
      Smt.Solution.Unsat
    ) else (
      match Smt.Theory.model model_pairs with
      | None ->
          print_endline "Theory found no valid model.";
          Smt.Solution.Unsat
      | Some int_model ->
          print_endline "Combined theory model:";
          Hashtbl.iteri int_model ~f:(fun ~key ~data ->
            Printf.printf "  %c = %d\n" (Char.of_int_exn key) data);

          let model = model_of_pairs model_pairs in
          Smt.Solution.Sat model
    )
