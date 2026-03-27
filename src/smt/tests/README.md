# /smt/tests
How to run scripts:

1. `bench_solver.ml` benchmarks Blue3 on formula text input:
```bash
cat f2.txt | dune exec ./bench_solver.exe -- 100 2>&1 | tail -n +3 > bench_solver.sql
```

2. `compare_z3.ml` compares Blue3 solve time vs Z3 on formula text input:
```bash
cat f2.txt | dune exec ./compare_z3.exe -- 100 2>&1 | tail -n +3 > compare_z3.sql
```
