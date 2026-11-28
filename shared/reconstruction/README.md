# Shared Lean project for Papers 2 and 3

The two papers share one pinned Lean project, test suite, and verification record. The manuscripts and paper-specific supplements live in their respective paper directories.

| Preprint | Main result |
| --- | --- |
| [Rank lower bounds for node-dependent polynomial reconstruction in SAT counting](../../node-dependent-reconstruction/paper/paper_polynomial_recovery.pdf) · [TeX](../../node-dependent-reconstruction/paper/paper_polynomial_recovery.tex) | For physical-variable layouts that can vary at each interpolation point, principal-submatrix and mismatch inequalities bound the ranks of the actual measurements. On a bounded-occurrence graph family they give visit lower bounds for the specified counting routine. |
| [Ternary Measurements for Paired Local Recovery](../../ternary-local-recovery/paper/paper_ternary_codes.pdf) · [TeX](../../ternary-local-recovery/paper/paper_ternary_codes.tex) | A central sender attains the binary minimum ranks $(4^q-1)/3$ at degree zero and $q+\lceil q/2\rceil+2$ at degree $q-2$. For each fixed even alphabet size $r$, the optimal degree-zero measurement fraction tends to $(r-1)/(2r-1)$. |

The first paper assumes visits to all Boolean-reachable measurement tuples, the prescribed Taylor subsets, and the assignments of a largest group. The bounds concern one such interpolation call. The second paper studies the full paired array with side information at each slot. Its exact binary endpoint results permit measurements across swap orbits.

## Read and reproduce the proofs

The [theorem index](THEOREMS.md) maps manuscript statements to source declarations. The two-paper project uses Lean 4.24.0 and a [pinned Mathlib revision](formal/lake-manifest.json). Run from this directory with Elan, Git and Python 3 installed:

```sh
cd formal
lake exe cache get
cd ..
python verify.py --logs ./replay
```

The verifier builds every local Lean module, enumerates the public theorem declarations in those modules, and runs `#print axioms` for each one. Enumeration includes Lean-generated public equations. The [recorded run](verification/result.txt) links the [build](verification/build.txt), [axiom output](verification/axioms.txt), and [source hashes](verification/source-sha256.txt) to the released files.

The [exact finite checks](tests) reproduce the examples in the papers. Install the Python dependency in [requirements.txt](tests/requirements.txt) before running the scripts. The additional finite-field checker evaluates the binary-valued encoder against the original recovery equations in characteristic two.

## Research status and attribution

See the repository-wide [contribution disclosure](../../AI_DISCLOSURE.md).
