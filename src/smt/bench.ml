open Smt.Formula
open Core

let lia_table_to_string tbl ~string_of_key =
  let entries =
    Map.to_alist tbl
    |> List.map ~f:(fun (key, data) ->
         let lower =
           Option.value_map data.lower ~default:"_" ~f:Int.to_string
         and upper =
           Option.value_map data.upper ~default:"_" ~f:Int.to_string
         and neq =
           data.neq |> List.map ~f:Int.to_string |> String.concat ~sep:","
         in
         sprintf "  %s -> {lower=%s; upper=%s; neq=[%s]}"
           (string_of_key key) lower upper neq)
    |> String.concat ~sep:"\n"
  in
  sprintf "LIA table:\n{\n%s\n}" entries

open Smt.Formula_2
(* Example symbols *)
let a = AsciiSymbol.make_int "a"
let b = AsciiSymbol.make_int "b"
let c = AsciiSymbol.make_int "c"
let d = AsciiSymbol.make_int "d"
let e = AsciiSymbol.make_int "e"

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
  let open Smt.Formula in
  List.iteri formulas ~f:(fun i fml ->
    printf "======= Formula %d =======\n" (i + 1);
    let start_ns = Time_ns.now () in
    let tbl, simplified = simplify fml in
    let stop_ns = Time_ns.now () in
    let elapsed_ns = Time_ns.diff stop_ns start_ns |> Time_ns.Span.to_int_ns in

    printf "Time: %d ns\n" elapsed_ns;
    printf "LIA table: %s\n"
      (lia_table_to_string tbl
        ~string_of_key:(fun k -> Char.of_int_exn k |> Char.to_string));
    printf "Original: %s\n" (List.map fml ~f:to_string |> String.concat ~sep:" ^ ");
    printf "Simplified: %s\n\n"
      (List.map simplified ~f:to_string |> String.concat ~sep:" ^ ");
  )
;;
