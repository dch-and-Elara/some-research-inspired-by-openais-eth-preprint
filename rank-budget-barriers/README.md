# Rank-Budget Barriers for Interpolation Algorithms

The paper studies how much rank a prescribed interpolation procedure can recover from local data. It proves bounds for nonuniform Hermite jets, attainable Boolean measurements, affine combinations across layouts and the literal root loop of the printed Appendix D evaluator.

[Paper (PDF)](paper/rank_budget_barriers.pdf) · [LaTeX source](paper/rank_budget_barriers.tex) · [Theorem index](THEOREMS.md) · [Kernel audit](verification/joint-kernel.txt)

## What changed in this edition

The supplement proves the Section 11 visit bound for **every** physical packing satisfying the source collision inequality and **every** pin input to that same packing. It also proves that the printed conditional-expectation method satisfies the inequality for any minimizing tie rule. The order of the size threshold, layout and input quantifiers appears in [the final Lean theorem](formal/P5EveryPrintedRoot.lean). Section 4.5 now explicitly carries the direct MAIN rank witness from the degree of the actual polynomial to the larger window used by the source.

The Section 8 construction uses one MAIN coordinate and one D coordinate. The proposed additional simultaneous same-method coordinates from the working draft have been reserved for separate verification. Earlier internal checkpoint tables are replaced by the theorem index and this release's audit. The high-order sparse MAIN rank argument uses the proved terminal parity. The source fixed-density bit-time upper bound and the existence of expander families are cited external results. The new lower bound counts visits of the literal evaluator.

## Reproduction

Install the Lean toolchain specified in [formal/lean-toolchain](formal/lean-toolchain). With Python 3, Git and Lake available, run the following commands from this paper's directory.

```sh
cd formal
lake exe cache get
cd ..
python verify.py
```

The verifier checks all 614 Lean source digests, the nine dependency revisions and the toolchain, runs the default Lake build, and imports every module into a single environment to check axiom dependencies. The 609 C17 modules were independently compiled from source into a fresh object directory. Five supplementary modules were compiled against those objects with warnings treated as errors. The combined audit inspected 12,042 project declarations, including 8,046 theorem declarations, and found zero local axioms. Its transitive axiom set consisted of `propext`, `Classical.choice`, and `Quot.sound`. The recorded compilation used the Lean compiler directly; the repository provides Lake as a reproduction entry point.

[Named axiom output](verification/axioms.txt) · [Module hashes](verification/modules.sha256) · [Dependency pins](verification/dependency-pins.json) · [C17 compilation results](verification/c17-replay.json)

The project owner supplied the research direction and the earlier model. AI systems contributed to the mathematical proofs, formalization and review. This is a public research draft.
