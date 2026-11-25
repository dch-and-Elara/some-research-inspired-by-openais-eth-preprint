# Rank lower bounds for node-dependent polynomial reconstruction in SAT counting

[Read the preprint](papers/paper_polynomial_recovery.pdf) · [LaTeX source](papers/paper_polynomial_recovery.tex) · [Theorem index](THEOREMS.md)

With physical-variable layouts that vary at each interpolation node, principal-submatrix and mismatch inequalities bound the actual measurement ranks. The runtime theorems count visits to Boolean-reachable measurement tuples, the prescribed Taylor subsets, and assignments of a largest group in one interpolation call. The construction also gives a bounded-occurrence family and a parsimonious extension of arbitrary CNFs.

## Read and reproduce the proofs

The [theorem index](THEOREMS.md) maps manuscript statements to source declarations. The project uses Lean 4.24.0 and a [pinned Mathlib revision](formal/lake-manifest.json). Run from this directory with Elan, Git and Python 3 installed:

```sh
cd formal
lake exe cache get
cd ..
python verify.py --logs ./replay
```

The verifier builds every local Lean module, enumerates the public theorem declarations in those modules, and runs `#print axioms` for each one. Enumeration includes Lean-generated public equations. The [recorded run](verification/result.txt) links the [build](verification/build.txt), [axiom output](verification/axioms.txt), and [source hashes](verification/source-sha256.txt) to the released files.

The [exact finite checks](tests) reproduce the layout examples. Run the Python scripts directly to compare their output with the recorded checks in [verification](verification).

## Research status and attribution

This is a research preprint. The project initiator supplied the questions and early conjectures. AI assistants contributed substantially to the proofs, computational checks, Lean code and manuscript preparation. The manuscript describes its antecedents and open problems. Independent human peer review and a determination of publication priority remain outstanding.
