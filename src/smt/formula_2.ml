open Smt.Sat

(** Use same type as Smt.Formula.t *)
type ('a, 'k) t = ('a, 'k) Smt.Formula.t

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


let solve (exprs : (bool, 'k) t list) : 'k Smt.Solution.t =
    let open Core in
    let open Smt.Formula in

    Printf.printf "\027[1;34m======= SMT solve() run =======\027[0m\n";
    List.iteri exprs ~f:(fun i e ->
        Printf.printf "Expr %d: %s\n" (i + 1) (Smt.Formula.to_string e));
    print_endline "-----------------------------------";

    let rec collect_atoms : type a k. (bool, k) t list -> (a, k) t -> (bool, k) t list =
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
    print_endline "-----------------------------------";

    Printf.printf "CNF:\n";
    List.iteri cnf ~f:(fun i clause ->
        Printf.printf "  %d: %s\n" i
            (String.concat ~sep:" ∨ "
                (List.map clause ~f:(function
                    | Pos x -> Printf.sprintf "v%d" x
                    | Neg x -> Printf.sprintf "¬v%d" x))));
    match dpll equal [] cnf with
    | None ->
        print_endline "\027[1;31mResult: UNSAT\027[0m";
        print_endline "-----------------------------------\n";
        Smt.Solution.Unsat
    | Some assignment ->
        print_endline "\027[1;32mResult: SAT\027[0m";
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


open Core

module AsciiSymbol = Smt.Symbol.Make(struct
    type t = string
    let uid (s : string) =
        String.fold s ~init:0 ~f:(fun acc c -> acc + Char.to_int c)
end)

let trim = String.strip

let tokenize (s : string) : string list =
    let buf = Buffer.create 16 in
    let toks = ref [] in
    let push () =
        if Buffer.length buf > 0 then (
            toks := Buffer.contents buf :: !toks;
            Buffer.clear buf
        )
    in
    String.iter s ~f:(fun c ->
        match c with
        | '(' | ')' | '^' ->
            push ();
            toks := String.of_char c :: !toks
        | ' ' | '\t' -> push ()
        | _ -> Buffer.add_char buf c);
    push ();
    List.rev !toks
;;

let line_error count msg = sprintf "Line %d: %s" count msg

let rec parse_until_closing count toks depth acc =
    match toks with
    | [] ->
        failwith (line_error count "unclosed parenthesis")
    | ")" :: rest when depth = 0 ->
        (List.rev acc, rest)
    | ")" :: rest ->
        parse_until_closing count rest (depth - 1) (")" :: acc)
    | "(" :: rest ->
        parse_until_closing count rest (depth + 1) ("(" :: acc)
    | tok :: rest ->
        parse_until_closing count rest depth (tok :: acc)

let rec parse_arithmetic toks count : (int, 'k) Smt.Formula.t * string list =
    let open Smt.Formula in
    match toks with
    | "(" :: rest ->
        let inner_toks, rest_after = parse_until_closing count rest 0 [] in
        let e, _ = parse_arithmetic inner_toks count in
        parse_arith_tail e rest_after count

    | "-" :: t :: rest when Option.is_some (Int.of_string_opt t) ->
        (Const_int (- Int.of_string t), rest)

    | t :: rest when Option.is_some (Int.of_string_opt t) ->
        parse_arith_tail (Const_int (Int.of_string t)) rest count

    | t :: rest ->
        parse_arith_tail (Key (AsciiSymbol.make_int t)) rest count

    | [] -> failwith (line_error count "unexpected end in arithmetic")

and parse_arith_tail lhs toks count : (int, 'k) Smt.Formula.t * string list =
    let open Smt.Formula in
    let open Smt.Binop in
    match toks with
    | op :: rest when List.mem ["+"; "-"; "*"; "/"; "%"] op ~equal:String.equal ->
        let rhs, rest' = parse_arithmetic rest count in
        let bop =
            match op with
            | "+" -> Plus | "-" -> Minus | "*" -> Times
            | "/" -> Divide | "%" -> Modulus | _ -> failwith "unreachable"
        in
        parse_arith_tail (Binop (bop, lhs, rhs)) rest' count
    | _ -> (lhs, toks)

let parse_comparison toks count : (bool, 'k) t * string list =
    let open Smt.Formula in
    let lhs, rest = parse_arithmetic toks count in
    match rest with
    | op :: rest' when List.mem ["="; "!="; ">="; ">"; "<="; "<"] op ~equal:String.equal ->
        let rhs, rest'' = parse_arithmetic rest' count in
        let bop =
            match op with
            | "=" -> Binop (Equal, lhs, rhs)
            | "!=" -> Binop (Not_equal, lhs, rhs)
            | ">=" -> Binop (Greater_than_eq, lhs, rhs) 
            | ">" -> Binop (Greater_than, lhs, rhs)
            | "<=" -> Binop (Less_than_eq, lhs, rhs)
            | "<" -> Binop (Less_than, lhs, rhs)
            | _ -> failwith "unreachable"
        in (bop, rest'')
    | ls -> sprintf "expected comparison operator near %s" (List.to_string ls ~f:(String.to_string))
        |> line_error count
        |> failwith
;;

type ('a, 'k) expr =
    | BoolExpr of (bool, 'k) t
    | IntExpr  of (int, 'k) t

let rec parse_subexpr count toks : ('a, 'k) expr * string list =
    match toks with
    | "not" :: rest ->
        let e, rest' = parse_subexpr count rest in
        begin match e with
            | BoolExpr b -> (BoolExpr (Not b), rest')
            | IntExpr _ -> "cannot apply 'not' to arithmetic" |> line_error count |> failwith
            end
    | "(" :: rest ->
        let inner_toks, rest_after = parse_until_closing count rest 0 [] in
        let e, _ = parse_subexpr count inner_toks in
        begin match rest_after with
            | op :: _ when List.mem ["="; "!="; ">="; ">"; "<="; "<"] op ~equal:String.equal ->
                let combined = inner_toks @ rest_after in
                let e', rest'' = parse_comparison combined count in
                (BoolExpr e', rest'')
            | _ -> (e, rest_after)
            end
    | [] ->
        failwith (line_error count "unexpected end, missing closing parenthesis")
    | _ :: op :: _ when List.mem ["="; "!="; ">="; ">"; "<="; "<"] op ~equal:String.equal ->
        let e, rest' = parse_comparison toks count in
        (BoolExpr e, rest')
    | _ :: op :: _ when List.mem ["+"; "-"; "*"; "/"; "%"] op ~equal:String.equal ->
        let e, rest' = parse_arithmetic toks count in
        (IntExpr e, rest')

    | _ -> (BoolExpr (Key (AsciiSymbol.make_bool (List.hd_exn toks))), List.tl_exn toks)

let parse_formula count toks : (bool, 'k) Smt.Formula.t * string list =
    match parse_subexpr count toks with
    | BoolExpr b, rest -> (b, rest)
    | IntExpr _, _ -> "arithmetic cannot appear at top level" |> line_error count |> failwith

let of_string : type k. string -> (bool, k) Smt.Formula.t list =
    fun s ->
    let count = ref 0 in
    s
    |> String.split_lines
    |> List.filter_map ~f:(fun line ->
        count := !count + 1;
        line
        |> String.strip
        |> function 
        | ln when String.is_empty ln -> None 
        | ln -> Some (
            ln 
            |> tokenize 
            |> parse_formula !count
            |> fst 
        ))
