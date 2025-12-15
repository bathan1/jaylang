(** Professor Scott Smith's "Lucky Guess" split function. It
    Splits the [(bool, 'k) Formula.t] inequality FORMULA into
    2 separate cases of a [Less_than] and a [Greater_than].
    For instance, the expression [x != 123456] would result
    in a split of [x > 123456 ^ x < 123456].

    If FORMULA is not a disequality, then this throws,
    so you can only safely call this if either you
    know FORMULA is a disequality ahead of time or
    if [is_match FORMULA = true].

    ...

    Example:
    {[
    let key uid = uid |> Char.of_int_exn |> Char.to_string

    let expr = Not (Binop (Equal, AsciiSymbol.make_int 'a', Const_int 123456))
    
    let () = 
      split expr
      |> fun (left, right) ->
        printf "Left split is %s\n" (Formula.to_string left ~key);
        printf "Right split is %s\n" (Formula.to_string right ~key)

        (* Prints
           "Left split is (a < 123456)"
           "Right split is (a > 123456)"
        *)
    ]}

    ...

    Keeping it stupid simple since '25

    ...

    Is this stupid simple??
*)
let lucky_guess : 'k Formula.split_fn = function
  | Not (Binop (Equal, Key I l, Const_int r))
    | Not (Binop (Equal, Const_int r, Key I l))
    | Binop (Not_equal, Key I l, Const_int r)
    | Binop (Not_equal, Const_int r, Key I l) ->
    Some (
      Binop (Less_than, Key (I l), Const_int r),
      Binop (Greater_than, Key (I l), Const_int r)
    )
  | _ -> None
