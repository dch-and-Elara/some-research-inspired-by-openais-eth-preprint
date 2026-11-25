# Manuscript-to-Lean index

The links point to the definitions and proofs. The repository records the [axioms of the declarations](verification/axioms.txt) separately from the experiments in the manuscripts.

## Rank lower bounds for node-dependent polynomial reconstruction

| Manuscript statement | Lean declaration and scope |
| --- | --- |
| Physical model and Boolean-reachable image | [VisitRuntimeCosts](formal/VisitRuntimeCosts.lean) counts distinct Boolean subset sums of independent measurement columns and derives the three costs from visit witnesses. |
| Theorem 1, principal subsets, (3)–(4) | [principal_subset_imbalance](formal/LayoutBudget.lean) derives twice the stated inequality from the foreign-group row-space hypothesis. [normalized_nullity_budget](formal/DeterminantBudget.lean) bounds the sum of nullities at distinct sites. |
| Corollary 2, random restriction, (5) | [corollary_two](formal/LayoutMomentsPrincipal.lean) gives the denominator $48\sqrt{2G}$ after selecting candidate factors and averaging the principal inequality over half-subsets. |
| Theorem 3, arbitrary node count, (6) | [theorems3_and6_graph_family](formal/VisitRuntime.lean) constructs a shared infinite family of positive graph 2-CNFs of occurrence at most three. The first conclusion gives the $2^{\Omega(n^{2/3})}$ visit bound. |
| Theorem 4, mismatch bound, (7)–(9) | [mismatch_rank](formal/LayoutMismatch.lean) starts from the incidence model and works on any selected subset of nodes with $|T|>R$. The [packing argument](formal/LayoutMismatchPacking.lean) and [binomial count](formal/LayoutMismatchCount.lean) give the factor of two. |
| Corollary 5, many high-rank nodes, (10) | [corollary_five](formal/LayoutMomentsMismatch.lean) proves the average bound for each eligible node set and the $Q-k+1$ individual conclusion. |
| Theorem 6 and Section 6 | [theorems3_and6_graph_family](formal/VisitRuntime.lean) gives $\log T=\Omega(n\log\log n/\sqrt{\log n})$ under $r^{2Q}\le n^A$. The final conclusion proves the arbitrary-node bound when a largest group is scanned at every node. [VisitRuntimeNumerical](formal/VisitRuntimeNumerical.lean) handles the Taylor floor, cap and bounded-node cases. |
| Appendix A | [exists_expanding_graph and exists_parsimonious_expanding_extension](formal/ExpansionGraph.lean) prove the graph existence and parsimonious extension results. [parsimonious_extension_runtime](formal/VisitRuntime.lean) applies the visit bounds to the padded formula and includes size and occurrence bounds. |
| Signed graph formulas | [VisitSigned](formal/VisitSigned.lean) proves the exact pre-substitution degree $2|E|$, agreement with the Boolean satisfaction indicator for arbitrary literal signs, and transfer of the visit bounds. [ReleaseLayoutSigned](formal/ReleaseLayoutSigned.lean) specializes the arbitrary-schedule family with constants independent of the schedule exponent. |
| Numerical steps and extension construction time | [ReleaseLayoutNumerical](formal/ReleaseLayoutNumerical.lean) verifies the schedule cap, binomial estimate and entropy margin used in the proof. [ExpansionGraphCostConformance](formal/ExpansionGraphCostConformance.lean) gives a linear word-record operation bound for a supplied edge list, proves parsimony and checks agreement with the extension up to gate renaming. |
