# Some Research Inspired by OpenAI’s ETH Preprint

These papers study local polynomial reconstruction, shared measurements, rank bounds for interpolation algorithms that count satisfying assignments, and sample bounds for sparse interpolation. The starting point is the interpolation method in OpenAI’s [preprint on the Exponential Time Hypothesis](https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026).

| Paper | Lean verification |
| --- | --- |
| [Optimal Degrees for Local Polynomial Reconstruction on the Boolean Cube](paper/paper.pdf) | [Theorem index](FORMALIZATION_SCOPE.md) · [Verification record](VERIFICATION.md) |
| [Rank lower bounds for node-dependent polynomial reconstruction in SAT counting](reconstruction-studies/papers/paper_polynomial_recovery.pdf) | [Theorem index](reconstruction-studies/THEOREMS.md#rank-lower-bounds-for-node-dependent-polynomial-reconstruction) · [Verification record](reconstruction-studies/verification/result.txt) |
| [Ternary Measurements for Paired Local Recovery](reconstruction-studies/papers/paper_ternary_codes.pdf) | [Theorem index](reconstruction-studies/THEOREMS.md#ternary-measurements-for-paired-local-recovery) · [Verification record](reconstruction-studies/verification/result.txt) |
| [A Root-Separation Barrier for Tensor-Interpolation SAT Algorithms](root-separation/paper/root_separation.pdf) | [Theorem index](root-separation/THEOREMS.md) · [Verification record](root-separation/verification/result.txt) |
| [Rank-Budget Barriers for Interpolation Algorithms](rank-budget-barriers/paper/rank_budget_barriers.pdf) | [Theorem index](rank-budget-barriers/THEOREMS.md) · [Kernel audit](rank-budget-barriers/verification/joint-kernel.txt) |
| [Native Information and Nonlinear Reconstruction in Interpolation Counting](checked-retained-execution/paper/Paper6.pdf) | [Theorem index](checked-retained-execution/THEOREMS.md) · [Verification record](checked-retained-execution/VERIFICATION.md) |
| [Sharp Sample Bounds for Sparse Interpolation on Prescribed Arithmetic Progressions](sparse-interpolation/paper/Grenet.pdf) | [Theorem index](sparse-interpolation/COVERAGE.md) · [Verification record](sparse-interpolation/VERIFICATION.md) |

## Optimal Degrees for Local Polynomial Reconstruction on the Boolean Cube

How much can arbitrary shared linear measurements reduce the degree needed to reconstruct data on the Boolean cube? The symmetric ternary construction achieves the optimal leading constant even among all rational measurement matrices.

[Read the paper (PDF)](paper/paper.pdf) · [LaTeX source](paper/paper.tex) · [Theorem index](FORMALIZATION_SCOPE.md)

For a cube of dimension $q$, the budget is $2^q/q^\gamma$ shared measurements. Write $d_{q,\gamma}$ for the minimum under bit flips and coordinate permutations, $\delta_{q,\gamma}$ under bit flips alone, and $\eta_{q,\gamma}$ with unrestricted ternary measurements. Write $\eta^{\mathbb Q}_{q,\gamma}$ when arbitrary rational entries are allowed.

* **Theorem A.** The symmetric minimum is exactly a finite optimization over deleted Hamming-weight layers. The cost of deleting layer $j$ is $\binom{q}{j}$. The formalization treats arbitrary integer budgets and then specializes to the real-valued budget above.
* **Theorem B.** For every fixed real $\gamma>1/2$, as $q\to\infty$,
  $$d_{q,\gamma}^{\,2}/q=(2\gamma-1)\log q+\log(8/\pi)+o(1).$$
* **Theorem C.** For every fixed real $\gamma>1/2$, each of $\delta$, $\eta$ and $\eta^{\mathbb Q}$ satisfies
  $$\lim_{q\to\infty}\frac{b_{q,\gamma}^{\,2}}{q\log q}=2\gamma-1.$$
  Here $b$ denotes the chosen minimum. Section 7 proves the lower bound from the original half-cube condition using $g^{\mathsf T}Ph$ with $Ch=0$.
* **Equation (5).** All three minima satisfy the same second-order interval. Its width is $2\log\log q+O_\gamma(1)$ in squared degree divided by dimension. The exact second-order term is open for each of these models.

### Reproduce the Boolean-cube proofs

The project pins Lean 4.28.0 and its Mathlib revision. From the repository root, run

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The default build imports all proof modules. The last command prints the axioms used by the audited declarations. [Verification record](VERIFICATION.md) · [AI disclosure](AI_DISCLOSURE.md)

## Rank lower bounds for node-dependent polynomial reconstruction in SAT counting

At each interpolation point, a factor can read its own group of variables and shared linear measurements of the other groups. The groups and measurements may change from one point to the next. The paper bounds how much measurement rank this freedom still requires, using determinants of submatrices and a count of the points where a variable’s source and target groups disagree.

On an infinite family of positive 2-CNF formulas in which each variable occurs at most three times, one call with a balanced layout requires $2^{\Omega(n^{2/3})}$ visits, for any number of interpolation points. The bound applies to a routine that enumerates all Boolean-reachable measurement tuples, visits the prescribed Taylor subsets, and scans the assignments of a largest group. Here $n$ is the number of variables.

[Paper (PDF)](reconstruction-studies/papers/paper_polynomial_recovery.pdf) · [LaTeX source](reconstruction-studies/papers/paper_polynomial_recovery.tex) · [Lean theorem index](reconstruction-studies/THEOREMS.md#rank-lower-bounds-for-node-dependent-polynomial-reconstruction)

## Ternary Measurements for Paired Local Recovery

Each array entry is indexed by a pair of length-$q$ words. A receiver sees part of the array directly and must recover its output using measurements shared by all receivers. How many independent measurements suffice?

For a binary indexing alphabet over the rationals, the minimum rank at degree zero is $(4^q-1)/3$ for $q\ge 1$. At degree $q-2$ it is $q+\lceil q/2\rceil+2$ for $q\ge 2$. Both optima are attained using coefficients in $\{-1,0,1\}$. For example, at $q=3$, allowing degree one reduces the optimum from 21 measurements to 7.

[Paper (PDF)](reconstruction-studies/papers/paper_ternary_codes.pdf) · [LaTeX source](reconstruction-studies/papers/paper_ternary_codes.tex) · [Lean theorem index](reconstruction-studies/THEOREMS.md#ternary-measurements-for-paired-local-recovery)

## A Root-Separation Barrier for Tensor-Interpolation SAT Algorithms

How many products of local functions are needed to express a final model count? For each pin assignment on a cubic expander with $N$ vertices, the model count is a single bit recording whether every edge clause is satisfied. For the layouts covered by the full-group theorem, with alphabet size at least 27 and fixed positive expansion, any fixed signed sum recovering this bit needs $2^{\Omega(N/\sqrt{\log N})}$ products. Each product may choose its own retained coordinate.

Appendix C counts work in a specific execution. On sufficiently large simple cubic graphs, the specified sparse clause-network evaluator returns the exact count and performs at least $2^{N/(2\sqrt{\log_2 N})}$ digit updates at its root.

[Paper (PDF)](root-separation/paper/root_separation.pdf) · [LaTeX source](root-separation/paper/root_separation.tex) · [Lean theorem index](root-separation/THEOREMS.md)

## Rank-Budget Barriers for Interpolation Algorithms

This paper asks how much rank local interpolation data can retain when an algorithm combines them to recover a final value. It proves bounds for Hermite data at unequal precisions and for fixed affine combinations of local products across layouts. It also bounds the visits of a specified iterator when it enumerates only measurement tuples attainable on Boolean inputs.

Section 8 shows how one multiplication can recover the exact SAT count from two products of local functions. On the cloned input, both coordinates can come from one MAIN layout, both from one Appendix D packing, or one from each method. On the original uncloned input, levels 0 and 1 of a single Appendix D root suffice. Each local function reads only the signs in its assigned group. The linear evaluation cost applies to the terminal scan after preprocessing.

The Section 8 update independently recompiled 29 Lean modules and checked 125 named declarations for axiom dependencies. The combined audit imported all 643 modules of this paper and found no project-defined axioms. [Section 8 replay](rank-budget-barriers/verification/section8-replay.json) · [LaTeX source](rank-budget-barriers/paper/rank_budget_barriers.tex) · [Reproduction instructions](rank-budget-barriers/README.md#reproduction)

## Native Information and Nonlinear Reconstruction in Interpolation Counting

Which information survives finite-precision interpolation, and how much does it cost to acquire the registers used for counting? The paper gives exact capacity results for specified decoder interfaces. For two prescribed probe orders, it also connects the returned value to the original CNF model count and bounds the measured steps of that same execution under explicit preparation, width and local cost assumptions.

[Paper (PDF)](checked-retained-execution/paper/Paper6.pdf) · [LaTeX source](checked-retained-execution/paper/Paper6.tex) · [Browse all Lean modules](checked-retained-execution/formal/module-index/README.md) · [Verification](checked-retained-execution/VERIFICATION.md)

## Sharp sample bounds for sparse interpolation on prescribed arithmetic progressions

For polynomials with at most $t$ terms and unbounded degree, how many consecutive evaluations on a prescribed arithmetic progression determine the polynomial? Over a nonzero commutative ring with identity and torsion-free additive group, every progression with a non-zero-divisor step succeeds after $4t$ evaluations. For each such ring and step, some start requires all $4t$. The paper also determines the exact minimum for each rational normalized start.

[Paper (PDF)](sparse-interpolation/paper/Grenet.pdf) · [LaTeX source](sparse-interpolation/paper/Grenet.tex) · [Lean and reproduction instructions](sparse-interpolation/README.md)

## Contact

<dingchuhang26@stu.pku.edu.cn>
