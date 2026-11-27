# Papers 1–4: Lean closeout

The four papers and their supplements passed separate source rebuilds against [the pinned baseline](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/commit/affcf9b1dd4ae1bb66fe5d474a61f7c62781decc). The review compared the actual objects, quantifiers, assumptions, and conclusions. For execution-cost claims it checked that correctness and charging concern the same execution, in the stated cost unit.

- **Paper 1:** [Coverage and replay](01-boolean-cube/COVERAGE.md). 25 baseline modules, 13 supplement modules, 165 distinct axiom checks.
- **Paper 2:** [Filtration](02-measurement-filtration/SCOPE.md), [literal slot multiplicity](02-measurement-filtration/P2CloseoutLiteralLists.lean), [A.2 actual-output bridge](02-measurement-filtration/P2CloseoutA2Actual.lean), and [declaration checks](02-measurement-filtration/P2CloseoutAudit.lean). The A.2 bridge relates the actual generated CNF to its solution count, its construction charge in the specified word/record model, and the stated visit bounds under the paper's schedule hypotheses.
- **Paper 3:** [Literal Walsh construction](03-walsh-gaussian/SCOPE_WALSH.md) and [same-run Bareiss verification](03-walsh-gaussian/SCOPE_GAUSSIAN.md). Papers 2 and 3 share the 106-module baseline rebuild; the seven Paper 3 supplement modules have 44 named checks. Three published code experiments were rerun.
- **Paper 4:** [Proof and scope inventory](04-execution-charges/APPENDIX_AB_PROOF_ROUTE_INVENTORY.md). 180 baseline modules, 9 supplement modules, 1,802 distinct axiom checks. The external fee transfer retains its ordered-injection and unit-fee assumptions.

The only recorded axiom dependencies are drawn from `propext`, `Classical.choice` and `Quot.sound`. Paper 4 uses the [MSS graph-family existence theorem](https://annals.math.princeton.edu/2015/182-1/p07) as an external mathematical citation, not a Lean theorem in this project. This note does not certify arbitrary implementations or a new general bit-machine cost model.

SHA-256 of the A.2 Lean file: `1a77230fc93e5890bf5c200108d35867fb02858bab5d4378db66131055fb4280`.
