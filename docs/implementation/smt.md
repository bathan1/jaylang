# SMT Solving
At some point in a Jaylang program's lifetime, the Concolic Evaluator will need to check the 
satisfiability of some SMT expressions. Jaylang rolls its own SMT solver frontend for OCaml that 
integrates basic theory checks in hopes of "simplifying" its inputs. It uses [Z3](./z3.md) for the backend, 
although any SMT solver can be used in theory.
