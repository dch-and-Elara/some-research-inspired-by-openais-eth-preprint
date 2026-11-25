# A Root-Separation Barrier for Tensor-Interpolation SAT Algorithms

How many local products are needed to recover the final model count of a pinned expanding graph? This paper gives an exponential lower bound even when each term may choose its own eligible coordinate. A second lower bound applies to traces that materialize every term at positive cost.

[Paper (PDF)](paper/root_separation.pdf) · [LaTeX source](paper/root_separation.tex) · [Theorem index](THEOREMS.md) · [Lean verification record](verification/result.txt)

For the full-group bound the alphabet has at least 27 symbols. The layout has a nonempty set of retained coordinates and satisfies the collision and feasibility inequalities in the paper. The balanced-menu bound separately quantifies over eligible cuts. The execution theorem assumes a trace covering every term. Connecting this trace to the original SAT program, or obtaining a matching upper bound for that program, requires additional results. The paper develops the common-matching rank proof, the integral precision transfer, and the overlap and query-tree bounds. Its two appendices derive the rational Huber estimate and its edge-space version. The theorem index identifies the checked route and the classical comparisons.

## Reproduce the proofs

Use Python 3, Git and the toolchain in [formal/lean-toolchain](formal/lean-toolchain). Mathlib and its dependencies are pinned in the [Lake manifest](formal/lake-manifest.json). From this directory:

```sh
cd formal
lake exe cache get
cd ..
python verify.py --logs ./replay
python check_all.py --logs ./finite-replay
```

The first script runs `lake build`, enumerates the public theorem declarations, and executes `#print axioms` for those declarations and the [241 named checks](named-declarations.txt). The recorded run includes the [build log](verification/build.txt), [axiom output](verification/axioms.txt) and [source hashes](verification/source-sha256.txt). The scripts in [tests](tests) run additional finite examples, including examples from the research leading to this paper.

The finite checker verifies [the release manifest](SOURCE_MANIFEST.json) before and after its run. Its optional `--upstream-sources DIR` compares a directory of upstream TeX files with the four [reference hashes](upstream.json) and writes its report under `--logs`. [Recorded finite checks](verification/finite/result.txt)

## Research status and attribution

This research preprint grew out of a project studying local reconstruction in OpenAI’s October 25, 2026 ETH preprint. The project initiator directed the research question and release. AI assistants contributed to proof development, Lean implementation, mathematical review and preparation of the manuscript. The repository documents kernel checks and finite examples. Independent human peer review and a determination of publication priority remain outstanding.
