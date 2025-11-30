(* Nathan's Lucky Guess algorithm implementation.
   Courtesy of Dr. Scott Smith.

   ...

   Keeping It Stupid Simple since '25
*)

open Core

(** Static config variable that sets the max number of
    attempts {!Lucky.solve} can make.
*)
let __GUESS_COUNT__ = 2

type atom = {
  key : int;
  neqs : Int.Set.t
}

let bounce (center : int) (i : int) : int =
  let k = (i / 2) + 1 in
  if i mod 2 = 0 then
    center + k
  else
    center - k

