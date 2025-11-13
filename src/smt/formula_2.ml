open Sat

(** Use same type as Formula.t *)
type ('a, 'k) t = ('a, 'k) Formula.t

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

let rec tseitin (f : ('a, 'k) Formula.t)
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
    : 'k Model.t =
    { value =
        (fun (type a) (sym : (a, 'k) Symbol.t) ->
            match sym with
            | B _ ->
                let maybe_entry =
                    Core.List.find pairs ~f:(fun (atom, _) ->
                        match atom with
                        | Formula.Key s -> Symbol.equal s sym
                        | _ -> false)
                in
                (Core.Option.map maybe_entry ~f:snd : a option)
            | I _ ->
                (None : a option))
    }

let equal = Formula.equal
let const_int = Formula.const_int
let const_bool = Formula.const_bool
let symbol = Formula.symbol
let and_ (type k) (e_ls : (bool, k) t list) : (bool, k) t =
    let pos = Hashtbl.create (1 lsl 16) and neg = Hashtbl.create (1 lsl 16) in
    let stack = ref e_ls in
    let rec loop acc =
        match !stack with
        | [] -> (match acc with
            | [] -> Formula.Const_bool true
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

let is_const = Formula.is_const

let rec binop : type a b. (a * a * b) Binop.t -> (a, 'k) t -> (a, 'k) t -> (b, 'k) t =
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


let solve (exprs : (bool, 'k) t list) : 'k Solution.t =
    let open Core in
    let open Formula in

    let atom_table = Hashtbl.Poly.create ()
    and id_table = Hashtbl.create (module Int)
    and counter = ref 0 in

    let atoms =
        exprs
        |> List.concat_map ~f:(collect_atoms [])
        |> List.dedup_and_sort ~compare:Poly.compare
    in

    List.iter atoms ~f:(fun atom ->
        Hashtbl.set atom_table ~key:atom ~data:!counter;
        Hashtbl.set id_table ~key:!counter ~data:atom;
        incr counter);

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
    match dpll equal [] cnf with
    | None ->
        Solution.Unsat
    | Some assignment ->
        let model_pairs =
            List.filter_map assignment ~f:(fun (id, value) ->
                Option.map (Hashtbl.find id_table id) ~f:(fun atom ->
                    (atom, value)
                ))
        in

        if not (Theory.check model_pairs) then (
            Solution.Unsat)
        else
            match Theory.model model_pairs with
            | None ->
                Solution.Unsat
            | Some int_model ->
                let constraints = Theory.extract_constraints model_pairs in
                Option.iter (Theory.EUF.model { eqs = constraints.eqs; neqs = constraints.neqs; }) ~f:(fun eq_model ->
                    Hashtbl.iteri eq_model ~f:(fun ~key:x ~data:root ->
                        match Hashtbl.find int_model root with
                        | Some v -> Hashtbl.set int_model ~key:x ~data:v
                        | None ->
                            (match Hashtbl.find int_model x with
                                | Some v -> Hashtbl.set int_model ~key:root ~data:v
                                | None -> Hashtbl.set int_model ~key:x ~data:0)));


                let model = model_of_pairs model_pairs in
                Solution.Sat model


module AsciiSymbol = Symbol.Make(struct
    open Core
    type t = string
    let uid (s : string) =
        String.fold s ~init:0 ~f:(fun acc c -> acc + Char.to_int c)
end)

