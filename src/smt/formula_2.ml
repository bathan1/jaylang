let pos = Hashtbl.create (1 lsl 16) and neg = Hashtbl.create (1 lsl 16)
let and2 (e_ls : (bool, 'k) Smt.Formula.t list) : (bool, 'k) Smt.Formula.t =
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

(* let or2 (e_ls : (bool, 'k) Smt.Formula.t list) : (bool, 'k) Smt.Formula.t = *)
(*   let pos = Hashtbl.create (1 lsl 16) and neg = Hashtbl.create (1 lsl 16) in *)
(*   let stack = ref e_ls in *)
(*   let rec loop acc = *)
(*     match !stack with *)
(*     | [] -> (match acc with *)
(*              | [] -> Smt.Formula.Const_bool false *)
(*              | [e] -> e *)
(*              | _ -> Binop (Or, Const_bool false, Const_bool false)) *)
(*     | Const_bool true :: _ -> Const_bool true *)
(*     | Const_bool false :: tl -> stack := tl; loop acc *)
(*     | Binop (Or, e1, e2) :: tl -> stack := e1 :: e2 :: tl; loop acc *)
(*     | (Not e as ne) :: tl -> *)
(*         stack := tl; *)
(*         if Hashtbl.mem neg e then Const_bool true *)
(*         else if Hashtbl.mem pos e then loop acc *)
(*         else (Hashtbl.add pos e (); loop (ne :: acc)) *)
(*     | e :: tl -> *)
(*         stack := tl; *)
(*         if Hashtbl.mem pos e then Const_bool true *)
(*         else if Hashtbl.mem neg e then loop acc *)
(*         else (Hashtbl.add neg e (); loop (e :: acc)) *)
(*   in *)
(*   loop [] *)

(* test begins here *)
module Key : Smt.Symbol.KEY with type t = string = struct
    type t = string

    let uid (t : t) : int =
        Hashtbl.hash t
end

module Symbol_string = Smt.Symbol.Make(Key)

open Core

let bench ~runs label (f : unit -> 'a) =
  ignore (f ());

  let total = ref Time_ns.Span.zero in
  let min_  = ref Time_ns.Span.max_value_representable in
  let max_  = ref Time_ns.Span.min_value_representable in

  for _ = 1 to runs do
    let t0 = Time_ns.now () in
    ignore (Sys.opaque_identity (f ()));
    let dt = Time_ns.diff (Time_ns.now ()) t0 in
    total := Time_ns.Span.( !total + dt );
    if Time_ns.Span.( dt < !min_ ) then min_ := dt;
    if Time_ns.Span.( dt > !max_ ) then max_ := dt;
  done;

  let total_ns =
    Time_ns.Span.to_int63_ns !total |> Int63.to_float
  in
  let min_ns =
    Time_ns.Span.to_int63_ns !min_  |> Int63.to_float
  in
  let max_ns =
    Time_ns.Span.to_int63_ns !max_  |> Int63.to_float
  in
  let avg_ns = total_ns /. float runs in

  printf "%-6s runs=%d  avg=%.3f µs  min=%.3f µs  max=%.3f µs\n"
    label runs (avg_ns /. 1e3) (min_ns /. 1e3) (max_ns /. 1e3)

let key s : (bool, string) Smt.Formula.t = Smt.Formula.Key (Symbol_string.make_bool s)

let mk_tail n : (bool, string) Smt.Formula.t list =
  List.init n ~f:(fun i -> key (Int.to_string i))

let front_contradiction n : (bool, string) Smt.Formula.t list =
  key "x" :: Not (key "x") :: mk_tail n

let end_contradiction n : (bool, string) Smt.Formula.t list =
  key "x" :: mk_tail n @ [ Not (key "x") ]

let no_contradiction n : (bool, string) Smt.Formula.t list =
  key "x" :: mk_tail n

let () =
    (* (not (b = a)) ^ (d = c) *)
    (* let a = key "a" in *)
    (* let b = key "b" in *)
    (* let c = key "c" in *)
    (* let d = key "d" in *)
    (* let expr = [ *)
    (*     Smt.Formula.Not (Binop (Equal, b, a)); *)
    (*     Binop (Equal, d, c) *)
    (* ] in *)
    (* let result = and2 expr in *)
    let n = 100 in
    let f_front = front_contradiction n in
    let f_end   = end_contradiction   n in
    let f_none  = no_contradiction    n in

    bench ~runs:10 "and_  front" (fun () -> Smt.Formula.and_ f_front);
    bench ~runs:10 "and2  front" (fun () -> and2 f_front);

    bench ~runs:5  "and_  end  " (fun () -> Smt.Formula.and_ f_end);
    bench ~runs:5  "and2  end  " (fun () -> and2 f_end);

    bench ~runs:3  "and_  none " (fun () -> Smt.Formula.and_ f_none);
    bench ~runs:3  "and2  none " (fun () -> and2 f_none)

