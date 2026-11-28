# A Root-Separation Barrier for Tensor-Interpolation SAT Algorithms

How many local products are needed to recover the final model count of a pinned expanding graph? This paper gives an exponential lower bound even when each term may choose its own eligible coordinate. A second lower bound applies to traces that materialize every term at positive cost.

[Paper (PDF)](paper/root_separation.pdf) · [LaTeX source](paper/root_separation.tex) · [Theorem index](THEOREMS.md) · [Lean verification record](verification/result.txt)

For the full-group bound the alphabet has at least 27 symbols. The layout has a nonempty set of retained coordinates and satisfies the collision and feasibility inequalities in the paper. The balanced-menu bound separately quantifies over eligible cuts. Appendices A and B derive the rational Huber estimate and its edge-space version.

Corollary 3 assumes a trace covering every term. Appendix C studies the printed sparse clause-network program on the same pinned formulas by counting its root accumulations directly. For every simple cubic graph with at least 20 vertices the modeled program returns the exact count. Above an explicit sufficient size threshold, the same run executes at least $2^{N/(2\sqrt{\log_2 N})}$ digit updates at its root. This is a lower bound for the specified execution. The public Lean model describes the mathematics of the recursive program and does not supply wall-clock timings or a total bit-time upper bound.

## Reproduce the proofs

Use Python 3, Git and the toolchain in [formal/lean-toolchain](formal/lean-toolchain). Mathlib and its dependencies are pinned in the [Lake manifest](formal/lake-manifest.json). From this directory:

```sh
cd formal
lake exe cache get
cd ..
python verify.py --logs ./replay
python check_all.py --logs ./finite-replay
```

The first script runs `lake build`, enumerates the public theorem declarations, and executes `#print axioms` for those declarations and the [named checks](named-declarations.txt). The recorded run includes the [build log](verification/build.txt), [axiom output](verification/axioms.txt) and [source hashes](verification/source-sha256.txt). The scripts in [tests](tests) run additional finite examples, including examples from the research leading to this paper.

The finite checker verifies [the release manifest](SOURCE_MANIFEST.json) before and after its run. Its optional `--upstream-sources DIR` compares a directory of upstream TeX files with the four [reference hashes](upstream.json) and writes its report under `--logs`. [Recorded finite checks](verification/finite/result.txt)

## Research status and attribution

This research preprint grew out of a project studying local reconstruction in OpenAI’s October 25, 2026 ETH preprint. The project initiator directed the research question and release. AI assistants contributed to proof development, Lean implementation, mathematical review and preparation of the manuscript. The repository documents kernel checks and finite examples. Independent human peer review and a determination of publication priority remain outstanding.

[Additional formalization and scope](supplements/APPENDIX_AB_PROOF_ROUTE_INVENTORY.md) · [AI disclosure](../AI_DISCLOSURE.md)
