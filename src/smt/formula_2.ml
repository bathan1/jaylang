module Solveable : Smt.Formula.SOLVABLE
  with type ('a, 'k) t := ('a, 'k) Smt.Formula.t = struct
    type ('a, 'k) t = ('a, 'k) Smt.Formula.t
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


    let equal a b = Core.phys_equal a b || Core.Poly.equal a b
    let const_int x = Smt.Formula.Const_int x
    let const_bool x = Smt.Formula.Const_bool x
    let symbol s = Smt.Formula.Key s
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
    let is_const (type a) (x : (a, 'k) t) : bool =
        match x with
        | Const_int _ | Const_bool _ -> true
        | _ -> false
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

    let solve (exprs : (bool, 'k) t list) : 'k Smt.Solution.t =
        (** Convenience so we don't have to assert f' type for each Binop *)
        let add_bool_binop acc (op : _ Smt.Binop.t) e1 e2 =
            let f' : (bool, _) t = Binop (op, e1, e2) in
            f' :: acc
        in
        let rec collect_atoms : type a k. (bool, k) t list -> (a, k) t -> (bool, k) t list =
            fun acc f -> match f with
                | Const_bool _ | Const_int _ -> acc
                | Key (B _) -> f :: acc
                | Key (I _) -> acc
                | Not e -> collect_atoms acc e
                | And es -> List.fold_left es ~init:acc ~f:collect_atoms
                | Binop (Equal, e1, e2) ->
                    add_bool_binop acc Equal e1 e2
                | Binop (Less_than, e1, e2) ->
                    add_bool_binop acc Less_than e1 e2
                | Binop (Greater_than, e1, e2) ->
                    add_bool_binop acc Greater_than e1 e2
                | Binop (Less_than_eq, e1, e2) ->
                    add_bool_binop acc Less_than_eq e1 e2
                | Binop (Greater_than_eq, e1, e2) ->
                    add_bool_binop acc Greater_than_eq e1 e2
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

        let rec to_cnf f : int cnf =
            match f with
            | Const_bool true -> []
            | Const_bool false -> [ [] ]
            | Key _ | Binop ((Equal | Less_than | Greater_than
                | Less_than_eq | Greater_than_eq), _, _) ->
                let id = Hashtbl.find_exn atom_table f in
                [ [Pos id] ]
            | Not e -> (
                match e with
                | Key _ | Binop ((Equal | Less_than | Greater_than
                    | Less_than_eq | Greater_than_eq), _, _) ->
                    let id = Hashtbl.find_exn atom_table e in
                    [ [Neg id] ]
                | _ ->
                    to_cnf (not_ e) )
            | And es -> List.concat_map es ~f:to_cnf
            | Binop (Or, e1, e2) ->
                let c1, c2 = to_cnf e1, to_cnf e2 in
                List.concat_map c1 ~f:(fun a ->
                    List.map c2 ~f:(fun b -> a @ b))
            | _ -> []
        in
        let cnf = List.concat_map exprs ~f:to_cnf in

        match dpll Int.equal [] cnf with
        | None -> Smt.Solution.Unsat
        | Some assignment ->
            let model_pairs =
                List.filter_map assignment ~f:(fun (id, value) ->
                    match Hashtbl.find id_table id with
                    | Some atom -> Some (atom, value)
                    | None -> None)
            in
            let model = model_of_pairs model_pairs in
            Smt.Solution.Sat model
end

