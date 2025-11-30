# SMT Solving
At some point in a Jaylang program's lifetime, the Concolic Evaluator needs to check the
satisfiability some expressions. Jaylang rolls its own SMT solver frontend for OCaml that
integrates basic theory checks in hopes of "simplifying" its inputs. We chose
[Z3](./z3.md) for the backend of our SMT solver.

## Integer Difference Logic
`ceval` usually doesn't need to solve complex expressions. Most of its expressions are in
the form `x - y <= c`:

```bash
(b < a) ^ (not (c = 123456)) ^ (not (d = 123456)) ^ (e = 123456)
(b < a) and (e = 123456)
```
