open Smt

(** [Typed_z3] with a solver frontend!

  {3 Basic usage}
  {[
    open Overlays
    open Smt
    open Smt.Formula
    open Smt.Binop
    open Smt.Symbol

    let make_key c = AsciiSymbol.make_int c

    module Bluejay = Blue3.Make ()

    let () =
      let formula = And [
        Binop (Less_than_eq, make_key 'a', Const_int 1);
        Binop (Less_than_eq, make_key 'b', Const_int 2);
        Binop (Equal, make_key 'a', make_key 'b')
      ] in
      formula
      |> Bluejay.solve
      |> function
        | Solution.Sat model -> (
          model
          |> Model.to_string
          |> print_endline
        )
  ]}
*)
module Make () = (struct
  include Typed_z3.Make ()

  let splits = [Splits.neq]
  let logics : (module Formula.LOGIC) list = [(module Difference)]
end)

module Default = Make ()

include Default
