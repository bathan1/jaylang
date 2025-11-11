open Formula_2

let hashtbl_to_string
    (tbl : ('k, 'v) Hashtbl.t)
    ~(string_of_key : 'k -> string)
    ~(string_of_val : 'v -> string)
    : string =
    let buf = Buffer.create 64 in
    Buffer.add_string buf "{";
    let first = ref true in
    Hashtbl.iter
        (fun k v ->
            if !first then first := false else Buffer.add_string buf "; ";
            Buffer.add_string buf (Printf.sprintf "%s -> %s"
                (string_of_key k)
                (string_of_val v)))
        tbl;
    Buffer.add_string buf "}";
    Buffer.contents buf

let () =
    try
        let a = AsciiSymbol.make_int "a" and b = AsciiSymbol.make_int "b" in
        let expr = [ 
            Smt.Formula.And [
                Binop (Equal, Key a, Const_int 123);
                Binop (Greater_than, Key b, Key a)
            ]
        ] in
        let hash, simplified = simplify expr in
        Printf.printf "hash is %s\n" (hashtbl_to_string hash
            ~string_of_key:(fun (key, _) -> key |> Char.chr |> Core.Char.to_string)
            ~string_of_val:Int.to_string
        );
        Printf.printf "simplified is %s\n" (
            List.fold_left (fun acc expr -> acc ^ (to_string expr)) "" simplified
        );
    with
        | e ->
        Printf.eprintf "Error: %s\n" (Core.Exn.to_string e);
        exit 1

