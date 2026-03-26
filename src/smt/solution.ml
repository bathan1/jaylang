type 'k t =
  | Sat of 'k Model.t
  | Unknown
  | Unsat

(** Turn SOLUTION into readable text with assignments printed
    based on callbacks SYMBOL and PP_ASSIGNMENT. *)
let to_string 
  (type a k)
  (solution : k t)
  ~(symbol : int -> (a, k) Symbol.t)
  ~(pp_assignment : (a, k) Symbol.t -> a -> string)
  : string
  = 
  match solution with
  | Unknown -> "Unknown"
  | Unsat -> "Unsat"
  | Sat solution ->
    Model.to_string solution ~symbol ~pp_assignment
