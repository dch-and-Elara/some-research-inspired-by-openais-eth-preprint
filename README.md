# Some Research Inspired by OpenAI’s ETH Preprint

These four papers study local polynomial reconstruction, shared measurements, and the cost of representing a SAT count by products of local functions. The starting point is the interpolation method in OpenAI’s [preprint on the Exponential Time Hypothesis](https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026).

| Paper | Lean verification |
| --- | --- |
| [Optimal Degrees for Local Polynomial Reconstruction on the Boolean Cube](paper/paper.pdf) | [Theorem index](FORMALIZATION_SCOPE.md) · [Verification record](VERIFICATION.md) |
| [Rank lower bounds for node-dependent polynomial reconstruction in SAT counting](reconstruction-studies/papers/paper_polynomial_recovery.pdf) | [Theorem index](reconstruction-studies/THEOREMS.md#rank-lower-bounds-for-node-dependent-polynomial-reconstruction) · [Verification record](reconstruction-studies/verification/result.txt) |
| [Ternary Measurements for Paired Local Recovery](reconstruction-studies/papers/paper_ternary_codes.pdf) | [Theorem index](reconstruction-studies/THEOREMS.md#ternary-measurements-for-paired-local-recovery) · [Verification record](reconstruction-studies/verification/result.txt) |
| [A Root-Separation Barrier for Tensor-Interpolation SAT Algorithms](root-separation/paper/root_separation.pdf) | [Theorem index](root-separation/THEOREMS.md) · [Verification record](root-separation/verification/result.txt) |

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
