# Optimal Degrees for Local Polynomial Reconstruction on the Boolean Cube

How much does coordinate-permutation symmetry cost when reconstructing data on a Boolean cube? This repository contains the paper and Lean proofs for reconstruction from shared linear measurements and coordinate half-cubes. The measurement row space is invariant under every single-coordinate bit flip.

[Read the paper (PDF)](paper/paper.pdf) · [LaTeX source](paper/paper.tex) · [Theorem index](FORMALIZATION_SCOPE.md)

For a cube of dimension $q$, the budget is $2^q/q^\gamma$ shared measurements. Write $d_{q,\gamma}$ for the minimum degree when the measurement space is also invariant under coordinate permutations, and $\delta_{q,\gamma}$ for the minimum under bit flips alone.

* **Theorem A.** The symmetric minimum is exactly a finite optimization over deleted Hamming-weight layers. The cost of deleting layer $j$ is $\binom{q}{j}$. The formalization treats arbitrary integer budgets and then specializes to the real-valued budget above.
* **Theorem B.** For every fixed real $\gamma>1/2$, as $q\to\infty$,
  $$d_{q,\gamma}^{\,2}/q=(2\gamma-1)\log q+\log(8/\pi)+o(1).$$
* **Theorem C.** For every fixed real $\gamma>1/2$, the same leading constant holds with bit-flip invariance alone:
  $$\lim_{q\to\infty}\frac{\delta_{q,\gamma}^{\,2}}{q\log q}=2\gamma-1.$$
* **Equation (5).** The formalization also proves both second-order bounds for $\delta_{q,\gamma}$. The exact second-order term in this general model remains open.

## Reproduce the proofs

The project pins Lean 4.28.0 and its Mathlib revision. From the repository root, run

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The default build imports all proof modules. The last command prints the axioms used by the audited declarations. [Verification record](VERIFICATION.md) · [AI disclosure](AI_DISCLOSURE.md)
