
type 'k t =
  | Sat of 'k Model.t
  | Unknown
  | Unsat

let to_string : type k. k t -> string = function
  | Unsat -> "UNSAT"
  | Sat _ -> "SAT"
  | _ -> "idk"
