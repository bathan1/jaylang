open Formula_2

let intmap_to_string
    (tbl : lia_cst_t IntMap.t)
    ~(string_of_key : int -> string)
    : string =
    let buf = Buffer.create 128 in
    Buffer.add_string buf "{";
    let first = ref true in
    IntMap.iter
        (fun k v ->
            if !first then first := false else Buffer.add_string buf "; ";
            let lower_str =
                match v.lower with
                | Some l -> Printf.sprintf "lower=%d" l
                | None -> "lower=_"
            in
            let upper_str =
                match v.upper with
                | Some u -> Printf.sprintf "upper=%d" u
                | None -> "upper=_"
            in
            let neq_str =
                if v.neq = [] then "neq=[]"
                else
                    let inner =
                        v.neq |> List.map string_of_int |> String.concat ","
                    in
                    Printf.sprintf "neq=[%s]" inner
            in
            Buffer.add_string buf
                (Printf.sprintf "%s -> {%s; %s; %s}"
                    (string_of_key k)
                    lower_str upper_str neq_str))
        tbl;
    Buffer.add_string buf "}";
    Buffer.contents buf

open Core
open Smt.Formula

let a = AsciiSymbol.make_int "a" 
and b = AsciiSymbol.make_int "b"
and c = AsciiSymbol.make_int "c"
and d = AsciiSymbol.make_int "d"
and e = AsciiSymbol.make_int "e";;

let a_eq_123456 = Binop (Equal, Key a, Const_int 123456)
let b_eq_a = Binop (Equal, Key a, Key b)
let b_lt_a = Binop (Less_than, Key b, Key a)
let b_gt_a = Binop (Greater_than, Key b, Key a)
let d_eq_c = Binop (Equal, Key d, Key c)
let b_eq_123456 = Binop (Equal, Key b, Const_int 123456)
let c_eq_123456 = Binop (Equal, Key c, Const_int 123456)
let d_eq_123456 = Binop (Equal, Key d, Const_int 123456)
let e_eq_123456 = Binop (Equal, Key e, Const_int 123456)

let formulas = [
    [ a_eq_123456 ];
    [ Not b_eq_a ];
    [
        And [
            Not b_eq_a;
            d_eq_c;
        ]
    ];
    [
        And [
            a_eq_123456;
            b_eq_123456;
        ]
    ];
    [
        And [
            a_eq_123456;
            Not b_eq_123456;
            c_eq_123456;
        ]
    ];
    [
        And [
            a_eq_123456;
            b_eq_123456;
            c_eq_123456;
        ]
    ];
    [
        And [
            b_lt_a;
            Not c_eq_123456;
            Not d_eq_123456;
            e_eq_123456;
        ]
    ];
    [
        And [
            a_eq_123456;
            Not b_eq_123456;
            c_eq_123456;
            d_eq_123456;
        ]
    ];
    [
        And [
            a_eq_123456;
            b_eq_123456;
            Not c_eq_123456;
            d_eq_123456;
        ]
    ];
    [
        And [
            a_eq_123456;
            b_eq_123456;
            c_eq_123456;
            d_eq_123456;
        ]
    ];
    [
        And [
            Not b_gt_a;
            Not b_lt_a;
            Not c_eq_123456;
            Not d_eq_123456;
            Not e_eq_123456;
        ]
    ];
]

let () =
    List.iteri formulas ~f:(fun i fml ->
        printf "======= Formula %d =======\n" (i + 1);
        let start_ns = Time_ns.now () in
        let tbl, simplified = simplify fml in
        let stop_ns = Time_ns.now () in
        let elapsed_ns = Time_ns.diff stop_ns start_ns |> Time_ns.Span.to_int_ns in

        printf "Time: %d ns\n" elapsed_ns;
        printf "LIA table: %s\n"
            (intmap_to_string tbl
                ~string_of_key:(fun k -> Char.of_int_exn k |> Char.to_string));
        printf "Original: %s\n" (List.map fml ~f:to_string |> String.concat ~sep:" ^ ");
        printf "Simplified: %s\n\n"
            (List.map simplified ~f:to_string |> String.concat ~sep:" ^ ");
    )
;;
