# SMT Solving
At some point in a Jaylang program's lifetime, the Concolic Evaluator needs to check the
satisfiability some expressions. Jaylang rolls its own SMT solver frontend for OCaml that
integrates basic theory checks in hopes of "simplifying" its inputs. We chose
[Z3](./z3.md) for the backend of our SMT solver.

## Integer Difference Logic
`ceval` usually doesn't need to solve complex expressions. Most of its expressions are in
the form `x - y <= c`:
```
(b < a) ^ (not (c = 123456)) ^ (not (d = 123456)) ^ (e = 123456)
```
`(b < a)` and `(e = 123456)`

From each [And] list element, we handle exactly 3 binary operations:
    {ol
        {-[<=]}
        {-[=]}
        {-[>=]}
    }
    For {i each} binary operator, we just need to handle 2 relations:
    {ol
        {- [Key, Key] }
        {- [Key, Const_int] (The reverse is also handled under the same match) }
    }

    That's {b 6} total cases to handle:
    {ol
        {- x ≤ y becomes x − y ≤ 0 }
        {- x ≤ c becomes x − 0 ≤ c }
        {- x = y becomes the {b pair} x − y ≤ 0, y − x ≤ 0 }
        {- x = c becomes the {b pair} x − 0 ≤ c, 0 − x ≤ −c }
        {- x ≥ y becomes y − x ≤ 0 }
        {- x ≥ c becomes 0 − x ≤ −c }
    }
    Any other {!Formula.t} type is ignored.

