open Binop
open Formula

let negate : (bool, 'k) Formula.t -> (bool, 'k) Formula.t = function
  | Binop (Less_than, Key I x, Key I y) ->
    Binop (Greater_than_eq, Key (I x), Key (I y))
  | Binop (Less_than, Key I x, Const_int c) ->
    Binop (Greater_than_eq, Const_int c, Key (I x))
  | Binop (Less_than, Const_int c, Key I x) ->
    Binop (Greater_than_eq, Key (I x), Const_int c)

  | Binop (Greater_than, Key (I x), Key (I y)) ->
    Binop (Less_than_eq, Key (I x), Key (I y))
  | Binop (Greater_than, Key (I x), Const_int c) ->
    Binop (Less_than_eq, Key (I x), Const_int c)
  | Binop (Greater_than, Const_int c, Key I x) ->
    Binop (Less_than_eq, Const_int c, Key (I x))

  | Binop (Less_than_eq, Key I x, Key I y) ->
    Binop (Greater_than, Key (I x), Key (I y))
  | Binop (Less_than_eq, Key I x, Const_int c) ->
    Binop (Greater_than, Const_int c, Key (I x))
  | Binop (Less_than_eq, Const_int c, Key I x) ->
    Binop (Greater_than, Key (I x), Const_int c)

  | Binop (Greater_than_eq, Key I x, Key I y) ->
    Binop (Less_than, Key (I x), Key (I y))
  | Binop (Greater_than_eq, Key I x, Const_int c) ->
    Binop (Less_than, Const_int c, Key (I x))
  | Binop (Greater_than_eq, Const_int c, Key I x) ->
    Binop (Less_than, Key (I x), Const_int c)

  | _ -> failwith "can't negate that"
;;
