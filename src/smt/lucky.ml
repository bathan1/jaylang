(* Nathan's Lucky Guess algorithm implementation.
   Courtesy of Dr. Scott Smith.

   ...

   Given some conjunctive formula F, with variables
   x1, x2, ..., xn. [Lucky] will attempt to make a
   guess on a SAT assignment
   *)

(** Static config variable that sets the max number of 
    attempts {!Lucky.solve} can make.
*)
let __TRY_COUNT__ = 1
