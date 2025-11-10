open Core

(** Handles symbolic Equality of Uninterpreted Functions. *)
module type EUF = sig
    type t = {
        eqs : (int * int) list;
        neqs : (int * int) list;
    }

    val normalize : (int * 'a * 'b) list -> t -> (int * 'a * 'b) list

    val check : t -> bool

    val model : t -> (int, int) Hashtbl.t option

    val print_constraints : t -> unit
end

(** Handles Linear Integer Arithmetric expressions. *)
module type LIA = sig
    val check :
        (int * Binop.iib Binop.t * int) list -> bool
    val model :
        (int * Binop.iib Binop.t * int) list -> (int, int) Hashtbl.t option
    val print_constraints :
        (int * Binop.iib Binop.t * int) list -> unit
end

module EUF : EUF = struct
    type t = { eqs: (int * int) list; neqs: (int * int) list; }
    type uf = { parent : (int, int) Hashtbl.t }

    let create () = { parent = Hashtbl.create (module Int) }

    let rec find uf x =
        match Hashtbl.find uf.parent x with
        | None -> x
        | Some p when p = x -> x
        | Some p ->
            let root = find uf p in
            Hashtbl.set uf.parent ~key:x ~data:root;
            root

    let union uf x y =
        let rx, ry = find uf x, find uf y in
        if rx <> ry then Hashtbl.set uf.parent ~key:ry ~data:rx

    let normalize constraints (t : t) =
        let uf = create () in
        List.iter t.eqs ~f:(fun (x, y) -> union uf x y);
        List.map constraints ~f:(fun (x, op, c) -> (find uf x, op, c))

    let check (t : t) =
        let parents = create () in
        List.iter t.eqs ~f:(fun (x, y) -> union parents x y);
        not (List.exists t.neqs ~f:(fun (x, y) -> find parents x = find parents y))

    let model (t : t) : (int, int) Hashtbl.t option =
        let uf = create () in
        List.iter t.eqs ~f:(fun (x, y) -> union uf x y);

        let conflict =
            List.exists t.neqs ~f:(fun (x, y) -> find uf x = find uf y)
        in
        if conflict then None
        else (
            let tbl = Hashtbl.create (module Int) in
            let roots = Hashtbl.create (module Int) in
            let next_val = ref 0 in
            let add_root root =
                if not (Hashtbl.mem roots root) then (
                    Hashtbl.set roots ~key:root ~data:!next_val;
                    incr next_val)
            in

            let all_syms =
                List.concat [ List.concat_map t.eqs ~f:(fun (x, y) -> [x; y]);
                    List.concat_map t.neqs ~f:(fun (x, y) -> [x; y]) ]
                |> List.dedup_and_sort ~compare:Int.compare
            in

            if List.is_empty all_syms then
                Some (Hashtbl.create (module Int))
            else (
                List.iter all_syms ~f:(fun x ->
                    let root = find uf x in
                    add_root root;
                    let v = Hashtbl.find_exn roots root in
                    Hashtbl.set tbl ~key:x ~data:v);
                Some tbl))

    let print_constraints ({ eqs; neqs }: t) =
        print_endline "Equality constraints:";
        if List.is_empty eqs && List.is_empty neqs then
            print_endline "  (none)"
        else
            List.iter eqs ~f:(fun (x, y) ->
                Printf.printf "  %c = %c\n"
                    (Char.of_int_exn x)
                    (Char.of_int_exn y));
        List.iter neqs ~f:(fun (x, y) ->
            Printf.printf "  %c != %c\n"
                (Char.of_int_exn x)
                (Char.of_int_exn y));
        print_endline "-----"
end

module LIA : LIA = struct
    type range = {
        mutable lower : int option;
        mutable upper : int option;
        mutable neq   : int list;
    }

    let update_range (r : range) (op : _ Binop.t) (c : int) =
        match op with
        | Binop.Less_than
            | Binop.Less_than_eq ->
            r.upper <- Some (min c (Option.value r.upper ~default:c))
        | Binop.Greater_than
            | Binop.Greater_than_eq ->
            r.lower <- Some (max c (Option.value r.lower ~default:c))
        | Binop.Equal ->
            r.lower <- Some c;
            r.upper <- Some c;
            r.neq   <- List.filter r.neq ~f:((<>) c)
        | Binop.Not_equal ->
            if not (List.mem r.neq c ~equal:Int.equal) then
                r.neq <- c :: r.neq

    let print_constraints constraints =
        print_endline "Integer constraints:";
        if List.is_empty constraints then
            print_endline "  (none)"
        else
            List.iter constraints ~f:(fun (x, op, c) ->
                let op_str =
                    match op with
                    | Binop.Less_than -> "<"
                    | Binop.Less_than_eq -> "<="
                    | Binop.Greater_than -> ">"
                    | Binop.Greater_than_eq -> ">="
                    | Binop.Equal -> "="
                    | Binop.Not_equal -> "!="
                in
                Printf.printf "  %c %s %d\n" (Char.of_int_exn x) op_str c);
        print_endline "-----"

    let check constraints =
        let ranges = Hashtbl.create (module Int) in
        List.iter constraints ~f:(fun (x, op, c) ->
            let r =
                Hashtbl.find_or_add ranges x
                    ~default:(fun () -> { lower = None; upper = None; neq = [] })
            in
            update_range r op c);

        Hashtbl.fold ranges ~init:true ~f:(fun ~key:_ ~data:{lower; upper; neq} acc ->
            match lower, upper with
            | Some l, Some u when l > u -> false
            | Some l, Some u ->
                not (List.exists neq ~f:(fun c -> c >= l && c <= u)) && acc
            | _ -> acc)

    let model constraints =
        if not (check constraints) then None
        else
            let ranges = Hashtbl.create (module Int) in
            List.iter constraints ~f:(fun (x, op, c) ->
                let r =
                    Hashtbl.find_or_add ranges x
                        ~default:(fun () -> { lower = None; upper = None; neq = [] })
                in
                update_range r op c);

            let model_tbl = Hashtbl.create (module Int) in
            Hashtbl.iteri ranges ~f:(fun ~key:x ~data:{lower; upper; neq} ->
                let chosen =
                    let base =
                        match lower, upper with
                        | Some l, Some u -> (l + u) / 2
                        | Some l, None -> l + 1
                        | None, Some u -> u - 1
                        | None, None -> 0
                    in
                    let rec adjust v =
                        if List.mem neq v ~equal:Int.equal then adjust (v + 1) else v
                    in
                    adjust base
                in
                Hashtbl.set model_tbl ~key:x ~data:chosen);
            Some model_tbl
end

type constraint_record = {
    eqs  : (int * int) list;
    neqs : (int * int) list;
    ints : (int * Binop.iib Binop.t * int) list;
}

let extract_constraints
    (model_pairs : ((bool, 'k) Formula.t * bool) list)
    : constraint_record =
    List.fold model_pairs
        ~init:{ eqs = []; neqs = []; ints = [] }
        ~f:(fun acc (atom, value) ->
            match atom, value with
            | Binop (Equal, Key x, Key y), true ->
                { acc with eqs = (Utils.Separate.extract x,
                    Utils.Separate.extract y) :: acc.eqs }

            | Binop (Equal, Key x, Key y), false ->
                { acc with neqs = (Utils.Separate.extract x,
                    Utils.Separate.extract y) :: acc.neqs }

            | Binop (Not_equal, Key (I x), Key (I y)), true ->
                { acc with neqs = (x, y) :: acc.neqs }

            | Binop (op, Key (I x), Const_int c), true ->
                { acc with ints = (x, op, c) :: acc.ints }

            | Not (Binop (Equal, Key x, Key y)), true ->
                { acc with neqs = (Utils.Separate.extract x, Utils.Separate.extract y) :: acc.neqs }
            | _ -> acc)
    |> fun result -> {
        eqs = List.dedup_and_sort ~compare:Poly.compare result.eqs;
        neqs = List.dedup_and_sort ~compare:Poly.compare result.neqs;
        ints = List.dedup_and_sort ~compare:Poly.compare result.ints
    }
;;

let model (model_pairs : ((bool, 'k) Formula.t * bool) list)
    : (int, int) Hashtbl.t option =
    let { eqs; ints; neqs } = extract_constraints model_pairs in
    let normalized_ints = EUF.normalize ints { eqs; neqs }in
    match LIA.model normalized_ints with
    | None -> None
    | Some int_model ->
        Option.iter (EUF.model { eqs; neqs }) ~f:(fun eq_model ->
            let pairs = Hashtbl.to_alist eq_model in
            List.iter pairs ~f:(fun (x, root) ->
                if x <> 0 && root <> 0 then (
                    match Hashtbl.find int_model root with
                    | Some v ->
                        Hashtbl.set int_model ~key:x ~data:v
                    | None ->
                        match Hashtbl.find int_model x with
                        | Some v ->
                            Hashtbl.set int_model ~key:root ~data:v
                        | None ->
                            if not (Hashtbl.mem int_model x) &&
                                not (Hashtbl.mem int_model root)
                            then Hashtbl.set int_model ~key:x ~data:0
                )));
        Some int_model

let check (model_pairs : ((bool, 'k) Formula.t * bool) list) : bool =
    let { eqs; neqs; ints } = extract_constraints model_pairs in

    EUF.print_constraints {eqs; neqs;};
    LIA.print_constraints ints;

    let normalized_ints = EUF.normalize ints {eqs; neqs;} in

    let eq_ok = EUF.check {eqs; neqs;} in
    let int_ok = LIA.check normalized_ints in

    eq_ok && int_ok

