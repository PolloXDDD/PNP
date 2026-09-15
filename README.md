# PNP — exact Boolean elimination

This repository investigates a constructive route to P versus NP through exact
Boolean variable elimination. It contains Python and C++ solvers, a one-cell
Google Colab notebook, a modular Lean 4 development, reproducible experiments,
and an English LaTeX paper.

**Result:** the elimination identity and witness recovery are exact. The dense
implementation has exponential worst-case cost in its elimination width.
**A general polynomial-time SAT algorithm and a proof of P=NP have not been obtained.**

## Use the solver

[Open the single-cell notebook in Google Colab](https://colab.research.google.com/github/PolloXDDD/PNP/blob/main/colab/PNP_exact_elimination.ipynb).
Run the cell, upload one or more `.cnf` files, and download each
`.cnf.solution.txt`. The complete solver is embedded in the cell; it needs no
third-party SAT package or repository download.

For a pasteable cell, use [colab/one_cell.py](colab/one_cell.py).
The notebook and cell are generated from the Python implementation by
`python3 scripts/build_colab.py`.

```bash
python3 src/sat_eliminate.py input.cnf --output solution.txt

g++ -std=c++17 -O3 -DNDEBUG src/sat_eliminate.cpp -o sat_eliminate
./sat_eliminate input.cnf --output solution.txt
```

Both solvers accept `--max-width`, `--max-cells`, `--timeout`, `--max-vars`,
and `--order ascending|min-degree`. Defaults are width 22, 50,000,000 cumulative
table cells, 60 seconds of solving time, and 1,000,000 declared variables.
The width includes the eliminated variable. The time check is cooperative;
parsing and writing are outside that budget. The table budget is not peak RAM.

| Result | Meaning | Process exit |
|---|---|---:|
| SATISFIABLE | A model was reconstructed and checked against the original clauses. | 10 |
| UNSATISFIABLE | Exact elimination established a contradiction. | 20 |
| UNKNOWN | A configured resource limit or allocation limit was reached. | 0 |
| ERROR | Invalid input or invocation; no SAT decision. | 2 |

SAT assignments appear on `v` lines and end with `0`. Limits never turn
UNKNOWN into UNSAT. A general shell may treat the SAT convention's nonzero
exit values 10 and 20 as failures even though they are valid solver outcomes.

## Mathematical core

Gather **all** factors containing a variable before projecting it:

$$
\exists x\,[H(y)\land G(x,y)]
=H(y)\land\bigl(G(0,y)\lor G(1,y)\bigr).
$$

Here H is independent of x. Store a feasible bit for every true projected
row, then traverse the records backwards to recover a model.
The implementations use Boolean tables, not DPLL, CDCL, randomness, or an
unproved optimization oracle.

For maximum recorded scope size b, the table-processing bound is
`O((m+n) b 2^b)`, before ordering and data-structure overhead. Constant width
gives a linear table-processing component. Arbitrary CNF does not have a
constant or logarithmic width guarantee.

[research/central_argument.md](research/central_argument.md) gives explicit
counterexamples for dense tables, auxiliary-free CNF, expanded ANF, affine
unions, and summaries containing only counts and proper marginals.
These are limitations of particular representations, not a proof of P≠NP.

## Formal development

The project pins Lean 4.19.0 and uses core Lean/Std. With that toolchain:

```bash
cd formal
lake build
```

Definitions, locality, projection, witness reconstruction, CNF semantics and
final theorems are organized into separate modules. The architecture follows
the separation of lemmas, final statements and build metadata in the
[OpenAI reference repository](https://github.com/openai/NavierStokesAndEuler).
The mathematical scope is different.

The Lean results concern the specified semantics. A proof that the Python/C++
parser, memory layout and compiled execution refine those definitions is
outside the current verification. Empirical differential tests cover that
boundary. No P=NP theorem or assumed universal polynomial bound is exported.

## Paper and experiments

- [English LaTeX source](paper/pnp_exact_elimination.tex)
- [Mathematical research](research/central_argument.md)
- Solvers: [Python](src/sat_eliminate.py), [C++17](src/sat_eliminate.cpp)

The validation report, generated benchmark data and complete theorem map are
being completed in this checkpoint. Timing measurements are not asymptotic
proofs. The existing MIT license is retained.
