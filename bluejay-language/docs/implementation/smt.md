# SMT Solving
There are many kinds of expressions an SMT formula can have, but
Jaylang is mainly concerned with simple arithmetic and boolean expressions.

For example:

```bash
(not (b > a)) ^ (not (b < a)) ^ (not (c = 123456)) ^ (not (d = 123456)) ^ (e = 123456)
```

Solving this means determining if the formula is satisfiable; that is, does there exist *any* assignment 
of the variables that satisfies the formula? If there is, then we call the formula **satifiable**. Otherwise
it is **unsatisfisable**.

So if I told you the above expression is satisfiable with the following assignments:

```bash
{
  a => 1
  b => 1
  c => 123455
  d => 123455
  e => 123456
}
```

How would you check my solution? You'd just plug in my assignments...

```bash
(not (1 > 1)) ^ (not (1 < 1)) ^ (not (123455 = 123456)) ^ (not (123455 = 123456)) ^ (123456 = 123456)
```

... and find that this evaluates out to `true`, so immediately you know this is **satisfiable**.

As you can see, *checking* a solution is easy — just plug and chug. So what about *finding* a solution? Is it just
as easy as checking one? Or at least similarly easy?

**Short answer:** no.

**Longer answer:** we don’t know — but probably not.

Checking a solution is easy: given N variable assignments, you simply plug in N values and evaluate the formula, which takes time proportional to N — i.e. polynomial time.

Finding a solution is harder. For general SMT formulas, we don’t know a polynomial-time algorithm for discovering satisfying assignments; in the worst case, solving can take exponential time.

That said, worst-case complexity only tells part of the story. Modern SMT solvers such as [Z3](https://z3prover.github.io/papers/z3internals.html) perform extremely well on the kinds of constraints produced by real programs, often solving them quickly in practice.

Jaylang uses [Z3](./z3.md) as its primary SMT solver, but also includes a small “mini” solver for simple formulas, which the rest of this page describes.

## Mini Solver main loop
Many of the SMT expressions Jaylang is concerned with are "stupid" simple formulas. You might
even call a lot of them trivial.

For example:

```bash
(a = b) ^ (not (a = 123456))
```

While we *could* make Z3 solve this, it's often faster to solve directly from the Bluejay code rather 
than from the Z3 shared library. This is (likely*) due to the type conversions
and memory management OCaml needs to perform when invoking an FFI.

>*TODO: Quantify cost of Z3 FFI invokation?

Rather than immediately send the formula to Z3, Jaylang will attempt to solve the formula itself.
The hope is that the mini solver can find a solution of [`SAT`](#) of [`UNSAT`](#) in a reasonable
amount of time. 

So even though the mini-solver isn't (nearly) as optimized as Z3's solver is, calling
a suboptimal implementation directly from the OCaml code is often faster than calling a better
implementation from a shared library.

The mini solver's loop goes something like this.

1. **Check** formula state for `UNSAT`.

    - If `UNSAT`, then just return that.
    - If `UNKNOWN`, then defer to Z3 and return that result.

<<< ../../../src/smt/formula.ml#solve_check{ocaml}

If we don't need to return, then the formula *may* be satisfiable, so the mini solver needs to..

2. **Split** the formula state into disjunctive (ORed) *left* and *right* branches, if such branches even exist:

```ocaml
match branch X.splits formula with
```

If there is no *right* branch, then we have no 
disjunctions to split on and can solve the formula 
as a whole:

<<< ../../../src/smt/formula.ml#solve_branch_leaf{ocaml}

Otherwise, we have 2 possibilities to check, either
of which can be satisfiable for the entire formula to
be satisfiable:

<<< ../../../src/smt/formula.ml#solve_branch_exists{ocaml}

Then with these branches, we can finish the iteration,
we just need to...

3. **Try** to solve the left branch, then **check** the solution.


<<< ../../../src/smt/formula.ml#solve_try{ocaml}

If `SAT`, we return our solution; our theory checkers were sufficient to solve the formula ourselves:

<<< ../../../src/smt/formula.ml#solve_try{2,3 ocaml}

Else if `UNSAT`, we *recursively* run this loop against
the right branch; maybe the right branch can be solved:

<<< ../../../src/smt/formula.ml#solve_try{5,6 ocaml}

Otherwise (if `UNKNOWN`), our mini solver isn't equipped to solve this
formula and will defer* solving to Z3:

<<< ../../../src/smt/formula.ml#solve_try{8,9 ocaml}

And that's it! The loop logic tries to hide as much of the actual "solving" logic up to external modules
so as to keep it generic as possible.

> [!WARNING]
> *Currently, the mini solver simply defers the original expression (and not the transformed branch) 
to Z3 to retain correctness. So in the worst case, if we're not able to solve the formula, 
then we've added extra solve time that Z3 could have used if we called Z3 immediately.

> [!WARNING]
> While this ^ is a tradeoff we can't really avoid, perhaps we can send a "reduced" formula
to Z3 if we're certain that the omitted variables doesn't affect the solution? Maybe something with *connected components* even? At least then, our solve attempt might not be a complete waste each time it needs to defer to Z3.

## Benchmarks
Benchmarks are just benchmarks, but they still matter for us.

### Binned Averages
The following graph shows [`solve`]() runtimes (in microseconds) for 760 formulas for both the mini-solver and Z3,
grouped in bins of 200.

Then it takes the average runtimes of each bin and plots it in a barchart, sorted in ascending order of the Z3 runtime
averages.

The green bar represents the mini solver and the red bar represents Z3.

![Mini vs. Z3 averaged runtimes](/difference_binned.png)
