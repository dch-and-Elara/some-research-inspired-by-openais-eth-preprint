# Verification of R119

The two release plans were independently checked with Lean 4.24.0 (commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`) and Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Each route was reconstructed from local source replay records. The final incremental run verifies the source, dependencies, command, object and axiom log of each retained module, recompiles the corrected leaves with warnings treated as errors, and executes the complete endpoint checks.

| Route | Verified modules | Newly compiled in the final run | Endpoint axiom checks | All project declarations audited | Theorem declarations |
| --- | ---: | ---: | ---: | ---: | ---: |
| Main | 3,136 | 1 | 36 | 61,873 | 32,494 |
| Binary probe order | 1,483 | 2 | 35 | 32,264 | 16,890 |

The counts are per route and include shared dependencies. The kernel audit enumerated constants by their defining module and followed their dependencies through the kernel environment. Each route has zero project-declared axioms. The full union of transitive axioms is `propext`, `Classical.choice` and `Quot.sound`. The binary route also passed both structural checks tying the model count and the step bound to the same execution.

The main plan includes historical alternatives with overlapping declaration names. Its audit used four environments with disjoint sets of assigned project modules. Each of the 3,136 modules is counted exactly once. The binary route was audited in a single environment. The [Lean inputs and output logs](verification/kernel-audits.zip), [per-group counts](verification/kernel.json), [replay summary](verification/formal-replay.json), and [source archive checks](verification/archive.json) accompany the [from-source replay instructions](formal/README.md).

The independent manuscript check compared the padded input size, the distinct subdivision count, the literal initial precision, and the preparation and root-contraction hypotheses with the Lean statements. The J2 review checked both native query interfaces and the layout shared by the joint endpoint. Appendix O distinguishes the two lawful probe orders and states the assumptions for the named active buffers. See the [theorem index](THEOREMS.md) for the hypotheses and claim boundaries. The [two-unit-clause calculation](verification/exact_cutoffs.py) reproduces the [archived exact cutoffs](verification/exact_cutoffs.csv).

The rebuilt manuscript has 105 pages. Nine historical finite-check programs distributed with this release reproduced their archived JSON outputs. Their [catalogue](paper/EVIDENCE_CATALOG.md) identifies the checks and the source files by hash. The standard [LaTeX manuscript](paper/Paper6.tex) and the actual [typesetting input](paper/typeset/README.md) are both included.
