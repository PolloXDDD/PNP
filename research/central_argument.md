# Exact elimination, compression attempts, and the remaining theorem

Status: mathematical research record, 2026-09-15. This project has not established
P = NP. The exact elimination identity is unconditional; a polynomial worst-case
bound for general CNF is not known here. The finite audits accompanying this file
check implementations and examples and do not replace the proofs below.

## 1. Exact local identity and witness recovery

Let `H(y)` contain all factors independent of a Boolean variable `x`, and let
`G(x,y)` be the conjunction of the factors in its bucket. Then

\[
\exists x\,[H(y)\land G(x,y)]
=H(y)\land(G(0,y)\lor G(1,y)).
\]

Proof: `H` has the same truth value in the two choices of `x`, so distributivity
factors it out of the disjunction. Let `R(y)=G(0,y) or G(1,y)`. When `R(y)` is
true, select `x=0` if `G(0,y)` is true, and otherwise select `x=1`. The selected
branch satisfies `G`. Repeating the identity preserves existence of a model.
After eliminating the variables, process these recorded choices in reverse;
each choice restores a satisfying extension. This proves exactness, not a
polynomial time bound.

A bucket with joined scope `S` requires `2^(|S|-1)` residual entries for a dense
table. Both residual and witness tables have this size. Direct evaluation may
add factors depending on the number and sizes of bucket factors. Polynomial
input size alone does not bound `|S|` logarithmically.

## 2. Why scope width is not universally logarithmic

Consider `K_n = AND_{i<j}(x_i OR x_j)`, with `n(n-1)/2` binary clauses. Whichever
variable is eliminated first occurs with every other variable; its first joined
bucket scope has size `n`. Thus a dense implementation enumerates `2^(n-1)`
rows at that step. Nevertheless `K_n` is satisfied by the all-true assignment.
Indeed its first projected bucket is constant true, which a symbolic
implementation can recognize without constructing a dense table. This example
refutes a universal small-scope claim for dense tables; it is not a lower bound
for every SAT algorithm, for dynamic semantic simplification, or for P vs NP.

## 3. Auxiliary-free CNF can grow exponentially after projection

For `n >= 2`, introduce `z_2,...,z_n` and encode
`z_2 = x_1 XOR x_2`, `z_i = z_(i-1) XOR x_i` for `3 <= i <= n`, and `z_n=1`.
Each XOR gate has four 3-clauses, giving `4(n-1)+1` clauses. Projecting out all
`z` gives odd parity on `x_1,...,x_n`.

Any exact CNF over only the `x` variables for odd parity has at least
`2^(n-1)` non-tautological clauses. To prove this, a non-tautological clause
omitting some `x_j` is falsified by two assignments differing only at `j`;
one of them has odd parity, so such a clause cannot be an implicate. Every
clause must therefore mention all `n` variables and can exclude only one
assignment. All `2^(n-1)` even assignments must be excluded. The bound is tight:
use one full clause for each even assignment. This is a restriction on
auxiliary-free CNF representation. Parity has linear circuits and small BDDs.

## 4. All proper projections and their counts can lose decisive correlations

Let `E_n` and `O_n` be even and odd parity relations. For every proper subset
`T` of the variables, both existential projections are the full Boolean cube
on `T`. More strongly, every fixed assignment to `T` has exactly
`2^(n-|T|-1)` extensions in either relation: choose all but one omitted bit
freely and use the last omitted bit to fix parity.

Consequently these projections and extension counts cannot distinguish
`E_n AND E_n` (satisfiable) from `E_n AND O_n` (unsatisfiable) if they are the
only information retained about each factor. Keeping all lower-order marginals
does not repair the lost highest-order correlation.

## 5. Algebraic normal form: exact operations, costly expansion

Work in the Boolean quotient ring over GF(2), with `x_i^2=x_i`. If
`f(x,y)=a(y)+x b(y)`, its two cofactors are `a` and `a+b`. Existential
quantification corresponds to Boolean OR, `u OR v = u+v+uv`, so

\[
\exists x\,f=a+b+ab.
\]

This uses `a^2=a` in the Boolean quotient. It is not ordinary polynomial
arithmetic over the reals. For `AND_{i=1}^t(x_i OR y_i)`, the ANF is
`PRODUCT_i(x_i+y_i+x_i*y_i)`. Because different factors use disjoint variables,
every choice of one of their three monomials gives a distinct product; no
GF(2) cancellation is possible. The expanded ANF has exactly `3^t` monomials
despite a CNF with `t` clauses. A factored circuit avoids this particular
expansion, but it still needs a separately proved bound for future projection
operations.

## 6. Affine systems, disjoint affine unions, and an unconditional obstruction

A consistent GF(2) linear system describes an affine solution space. Gaussian
elimination supports exact conjunction and existential projection of affine
systems in polynomial time. The ternary OR relation has seven points, so it
cannot itself be a nonempty affine space (whose cardinality is a power of two).

There is a constructive exact extension. Maintain a disjoint union of affine
systems. Intersect each component with a clause `l_1 OR ... OR l_k` using the
disjoint cases

`l_1=1`; `l_1=0,l_2=1`; ...; `l_1=...=l_(k-1)=0,l_k=1`.

Each case adds linear equations and is checked by Gaussian elimination.
Inconsistent cases disappear; surviving systems describe precisely all models.
With `t` clauses of width at most three, there are at most `3^t` components.
For disjoint positive OR3 clauses the unmerged construction has exactly `3^t`
components. Affine equations already present can greatly reduce this number.

Even optimal merging into arbitrary affine components cannot yield a
polynomial bound for this representation on the disjoint OR3 family. Its
solution set is `S_t=(GF(2)^3 \ {000})^t`, with `7^t` points. Let `A` be any
nonempty affine space contained in `S_t`. Project `A` onto any block of three
coordinates. The projection is affine and excludes `000`; hence it has at
most four points. Since `A` embeds into the Cartesian product of its block
projections, `|A| <= 4^t`. A union of `r` such components can cover at most
`r*4^t` points, so

\[
r\ge\left\lceil(7/4)^t\right\rceil.
\]

Overlapping components do not evade this counting argument. This proves an
exponential lower bound for exact solution-set representation by affine
unions, not for deciding these easy formulas. Factoring independent components
avoids storing their Cartesian product and is a concrete improvement; it does
not by itself control factors that become coupled during elimination.

## 7. A legitimate symbolic next step: two independent variable orders

Mengel (SAT 2023, Theorem 1) proves that BDD bucket elimination refutes the
standard pigeonhole formulas in polynomial time with row order inside BDDs and
column order for elimination. The same paper gives exponential behavior for
certain restrictions with those orders and for the variants using either of
these orders for both purposes. Thus the two orders are meaningful independent
design choices; their successful choice for one family supplies no universal
bound. [Primary paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2023.16)

Our next experiment should keep the already proved elimination semantics and
replace dense factors with reduced ordered BDDs. It should accept independent
BDD and elimination orders, measure *every intermediate* BDD and operation,
and replay row/column and same-order schedules on standard pigeonhole formulas
and restricted variants. SAT witnesses still require reverse cofactor choices.
Resource caps must yield UNKNOWN. A polynomial theorem would have to bound
construction, all intermediate operations, choosing the orders, and witness
extraction uniformly in input bit length.

For an elementary order audit, `AND_i(x_i OR y_i)` has an O(t)-size reduced BDD
under interleaved order `x_1,y_1,...,x_t,y_t`. Under the blocked order
`x_1,...,x_t,y_1,...,y_t`, the `2^t` assignments to the `x` variables leave
`2^t` distinct residual functions `AND_{i:x_i=0} y_i`. They cannot all share a
BDD state, giving an exponential representation lower bound for that order.
The code audits these two orders without calling an external SAT solver.

## 8. Scope of the sources

The elimination architecture is established work, not a newly discovered SAT
principle. Dechter's 1999 article is *Bucket elimination: A unifying framework
for reasoning*, Artificial Intelligence 113(1-2), 41-85,
[DOI](https://doi.org/10.1016/S0004-3702(99)00059-4). The separately accessible
[R48a author PDF](https://www.ics.uci.edu/~csp/R48a.pdf) is titled *Bucket
elimination: A unifying framework for probabilistic inference*. It also
discusses directional resolution and induced width, but it must not be
misidentified as the same article.

[Bryant (1986)](https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf) supplies the
canonical ordered decision-diagram framework and Boolean operations.
[Darwiche and Marquis (2002)](https://arxiv.org/abs/1106.1819) compare knowledge
compilation languages by succinctness and supported transformations. Neither
provides a polynomial-size representation closed under all operations needed
to solve arbitrary CNF here.

## 9. Reproducibility and the missing theorem

Run `python research/audit_central.py` from the repository root. It independently
checks finite instances of the identities, all-proper-marginal collision,
parity encoding, ANF expansion, affine-union construction and BDD order
separation. Results are written to `research/audit_results.json`.

What is established is exactness plus concrete representation obstructions.
To infer P=NP from this route, the project would need an explicit uniform
representation and algorithms whose *total* bit cost is polynomial for every
input CNF. A promise that residuals stay small, successful finite benchmarks,
or an identity with exponentially large intermediate operands is insufficient.
No such universal bound has been proved in this work.
