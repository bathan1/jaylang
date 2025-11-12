open Smt.Sat

(** Use same type as Smt.Formula.t *)
type ('a, 'k) t = ('a, 'k) Smt.Formula.t

let rec to_string : type a k. (a, k) t -> string = fun expr ->
    let open Core in
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

type lia_cst_t = {
    neq : int list;
    lower : int option;
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
    | Smt.Formula.Binop (op, Const_int v, Key (I x)) ->
        let curr =
            match IntMap.find_opt x acc with
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
        IntMap.add x cst acc
    | Smt.Formula.Binop (op, Key (I x), Const_int v) ->
        let curr =
            match IntMap.find_opt x acc with
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
        IntMap.add x cst acc
    | Smt.Formula.Binop (_, Key (I x), Key (I y)) ->
        let acc =
            if IntMap.mem x acc then acc else IntMap.add x empty_lia_cst acc
        in
        if IntMap.mem y acc then acc else IntMap.add y empty_lia_cst acc

    | Smt.Formula.Key key ->
        let x = Utils.Separate.extract key in
        if IntMap.mem x acc then acc else IntMap.add x empty_lia_cst acc

    | Smt.Formula.And ls ->
        List.fold_left next acc ls

    | _ -> acc
;;

let decide_eq :
    type k.
    (bool, k) t ->
    lia_cst_t ->
    lia_cst_t ->
    (bool, k) t
    = fun expr lcst rcst ->
    let open Smt.Formula in
    match (lcst.lower, lcst.upper, rcst.lower, rcst.upper) with
    | (Some xl, Some xu, Some yl, Some yu) when xl = xu && yl = yu ->
        Const_bool (xl = yl)
    | (Some xl, Some xu, Some yl, Some yu) when xu < yl || yu < xl ->
        Const_bool false
    | (Some xl, Some xu, _, _) when xl = xu && List.mem xl rcst.neq ->
        Const_bool false
    | (_, _, Some yl, Some yu) when yl = yu && List.mem yl rcst.neq ->
        Const_bool false
    | _ -> expr;;


let decide_neq :
    type k.
    (bool, k) t ->
    lia_cst_t ->
    lia_cst_t ->
    (bool, k) t
    = fun expr lcst rcst ->
    match decide_eq expr lcst rcst with
    | Const_bool true  -> Const_bool false
    | Const_bool false -> Const_bool true
    | _ -> expr
;;

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
        let x_cst = IntMap.find x acc
        and y_cst = IntMap.find y acc
        in
        let decided_expr = 
            (match op with
                | Equal -> decide_eq expr x_cst y_cst
                | Not_equal -> decide_neq expr x_cst y_cst
                | Less_than_eq
                    | Greater_than -> decide_gt x y x_cst y_cst
                | Greater_than_eq
                    | Less_than -> decide_gt x y y_cst x_cst)
        in
        Some decided_expr
    | And rest ->
        let simplified_subs =
            rest
            |> List.filter_map (sub acc)
        in
        let contains_false =
            List.exists (function Smt.Formula.Const_bool false -> true | _ -> false) simplified_subs
        in
        if contains_false then Some (Const_bool false)
        else
            let non_trivial =
                List.filter (function Smt.Formula.Const_bool true -> false | _ -> true) simplified_subs
            in
            begin match non_trivial with
                | [] -> Some (Const_bool true)
                | [single] -> Some single
                | ls -> Some (And ls)
                end
    | _ -> Some expr
;;

let simplify
    : type k.
    (bool, k) t list ->
    lia_cst_t IntMap.t * (bool, k) t list
    = fun exprs ->
    exprs
    |> List.fold_left next (IntMap.empty : lia_cst_t IntMap.t)
    |> fun tbl ->
    List.filter_map (fun el -> sub tbl el) exprs
    |> fun red -> (tbl, red)
;;

let rec tseitin (f : ('a, 'k) Smt.Formula.t)
    (fresh : ('a, 'k) t -> int)
    (cnf_acc : int cnf)
    (atom_table : (('a, 'k) t, int) Core.Hashtbl.t)
    : int * int cnf =
    let open Core in
    match f with
    | Const_bool true ->
        let v = fresh f in
        (v, [ [Pos v] ] @ cnf_acc)

    | Const_bool false ->
        let v = fresh f in
        (v, [ [Neg v] ] @ cnf_acc)

    | Key _ 
        | Binop ((Equal | Not_equal | Less_than | Less_than_eq
        | Greater_than | Greater_than_eq), _, _) ->
        let v =
            match Hashtbl.find atom_table f with
            | Some id -> id
            | None ->
                let id = fresh f in
                Hashtbl.set atom_table ~key:f ~data:id;
                id
        in
        (v, cnf_acc)

    | Not e ->
        let v_e, cnf_acc = tseitin e fresh cnf_acc atom_table in
        let v = fresh f in
        let new_clauses = [
            [Neg v; Neg v_e];
            [Pos v; Pos v_e];
        ] in
        (v, new_clauses @ cnf_acc)

    | And es ->
        let sub_vars, cnf_acc =
            List.fold_right es ~init:([], cnf_acc)
                ~f:(fun e (vs, acc) ->
                    let v_e, acc' = tseitin e fresh acc atom_table in
                    (v_e :: vs, acc'))
        in
        let v = fresh f in
        let new_clauses =
            List.map sub_vars ~f:(fun v_e -> [Neg v; Pos v_e])
            @
            [List.map sub_vars ~f:(fun v_e -> Neg v_e) @ [Pos v]]
        in
        (v, new_clauses @ cnf_acc)

    | Binop (Or, e1, e2) ->
        let v1, cnf_acc = tseitin e1 fresh cnf_acc atom_table in
        let v2, cnf_acc = tseitin e2 fresh cnf_acc atom_table in
        let v = fresh f in
        let new_clauses = [
            [Neg v; Pos v1; Pos v2];
            [Neg v1; Pos v];
            [Neg v2; Pos v];
        ] in
        (v, new_clauses @ cnf_acc)

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

let rec collect_atoms : type a k. (bool, k) t list -> (a, k) t -> (bool, k) t list =
    let open Core in
    fun acc f ->
    match f with
    | Const_bool _ | Const_int _ -> acc
    | Key (B _) -> f :: acc
    | Key (I _) -> acc
    | Not e -> collect_atoms acc e
    | And es -> List.fold_left es ~init:acc ~f:collect_atoms
    | Binop (Equal, e1, e2) -> Binop (Equal, e1, e2) :: acc
    | Binop (Less_than, e1, e2) -> Binop (Less_than, e1, e2) :: acc
    | Binop (Greater_than, e1, e2) -> Binop (Greater_than, e1, e2) :: acc
    | Binop (Less_than_eq, e1, e2) -> Binop (Less_than_eq, e1, e2) :: acc
    | Binop (Greater_than_eq, e1, e2) ->
        Binop (Greater_than_eq, e1, e2) :: acc
    | Binop (_, e1, e2) ->
        let acc = collect_atoms acc e1 in
        collect_atoms acc e2
;;


let solve (exprs : (bool, 'k) t list) : 'k Smt.Solution.t =
    let open Core in
    let open Smt.Formula in

    let atom_table = Hashtbl.Poly.create ()
    and id_table = Hashtbl.create (module Int)
    and counter = ref 0 in

    Printf.printf "\027[1;34m======= SMT solve() run =======\027[0m\n";
    List.iteri exprs ~f:(fun i e ->
        Printf.printf "Expr %d: %s\n" (i + 1) (to_string e));
    print_endline "-----------------------------------";

    let atoms =
        exprs
        |> List.concat_map ~f:(collect_atoms [])
        |> List.dedup_and_sort ~compare:Poly.compare
    in

    List.iter atoms ~f:(fun atom ->
        Hashtbl.set atom_table ~key:atom ~data:!counter;
        Hashtbl.set id_table ~key:!counter ~data:atom;
        incr counter);

    Printf.printf "\027[1;33mAtom table:\027[0m\n";
    Hashtbl.iteri atom_table ~f:(fun ~key:atom ~data:id ->
        Printf.printf "  %3d <-> %s\n" id (to_string atom));

    let fresh data =
        let v = !counter in
        incr counter;
        Hashtbl.set id_table ~key:v ~data;
        v
    in

    let cnf, top_vars =
        List.fold_left exprs ~init:([], []) ~f:(fun (cnf_acc, tops) e ->
            let v, cnf' = tseitin e fresh cnf_acc atom_table in
            (cnf', v :: tops))
    in

    let is_neg f =
        match f with
        | Not _ -> true
        | _ -> false
    in

    let top_clauses =
        List.map2_exn exprs top_vars ~f:(fun e v ->
            if is_neg e then [Neg v] else [Pos v])
    in
    let cnf = top_clauses @ cnf in

    Printf.printf "CNF generated: %d clauses, %d vars\n"
        (List.length cnf) !counter;
    Printf.printf "CNF:\n";
    List.iteri cnf ~f:(fun i clause ->
        Printf.printf "  %d: %s\n" i
            (String.concat ~sep:" ∨ "
                (List.map clause ~f:(function
                    | Pos x -> Printf.sprintf "v%d" x
                    | Neg x -> Printf.sprintf "¬v%d" x))));
    print_endline "-----------------------------------";

    match dpll equal [] cnf with
    | None ->
        print_endline "\027[1;31mSAT Result: UNSAT\027[0m";
        print_endline "-----------------------------------\n";
        Smt.Solution.Unsat
    | Some assignment ->
        print_endline "\027[1;32mSAT Result: SAT\027[0m";
        Printf.printf "Raw assignment (%d vars):\n" (List.length assignment);
        List.iter assignment ~f:(fun (id, value) ->
            Printf.printf "  v%-3d = %B\n" id value);
        print_endline "-----------------------------------";

        Printf.printf "ID table:\n";
        Hashtbl.iteri id_table ~f:(fun ~key ~data ->
            if Hashtbl.mem atom_table data then
                Printf.printf "  %d -> %s\n" key (to_string data));

        let model_pairs =
            List.filter_map assignment ~f:(fun (id, value) ->
                Option.map (Hashtbl.find id_table id) ~f:(fun atom ->
                    (atom, value)
                ))
        in

        if not (Smt.Theory.check model_pairs) then (
            print_endline
                "\027[1;31mTheory conflict — UNSAT after theory check.\027[0m";
            print_endline "-----------------------------------\n";
            Smt.Solution.Unsat)
        else
            match Smt.Theory.model model_pairs with
            | None ->
                print_endline "\027[1;31mTheory found no valid model.\027[0m";
                print_endline "-----------------------------------\n";
                Smt.Solution.Unsat
            | Some int_model ->
                let constraints = Smt.Theory.extract_constraints model_pairs in
                Option.iter (Smt.Theory.EUF.model { eqs = constraints.eqs; neqs = constraints.neqs; }) ~f:(fun eq_model ->
                    Hashtbl.iteri eq_model ~f:(fun ~key:x ~data:root ->
                        match Hashtbl.find int_model root with
                        | Some v -> Hashtbl.set int_model ~key:x ~data:v
                        | None ->
                            (match Hashtbl.find int_model x with
                                | Some v -> Hashtbl.set int_model ~key:root ~data:v
                                | None -> Hashtbl.set int_model ~key:x ~data:0)));

                print_endline "\027[1;36mCombined theory model:\027[0m";
                Hashtbl.iteri int_model ~f:(fun ~key ~data ->
                    if key >= 97 && key <= 122 then
                        Printf.printf "  %c = %d\n" (Char.of_int_exn key) data);
                print_endline "-----------------------------------\n";

                let model = model_of_pairs model_pairs in
                Smt.Solution.Sat model


module AsciiSymbol = Smt.Symbol.Make(struct
    open Core
    type t = string
    let uid (s : string) =
        String.fold s ~init:0 ~f:(fun acc c -> acc + Char.to_int c)
end)

