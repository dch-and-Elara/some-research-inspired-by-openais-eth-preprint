# Paper 2: literal Section 4 filtration overlay

This is an isolated supplement for Paper 2, the node-dependent reconstruction
manuscript under `reconstruction-studies`. It changes neither the published Lean
theorems nor the manuscript. The imported project's Lean bytes are pinned to
`95ad3fb52aeac8376ba835b76987ef5f9d6156d6`. The subsequent balance-wording
revision does not change the Section 4 equations treated here.

The audit found that the published Lean already proves Theorem 4 with the
same original hypotheses, via an independent slot-kernel map. It did not
state the printed filtration's codimension assertion as its own theorem.
This overlay formalizes that assertion directly and then checks the rest of
the printed dimension argument. It does not infer a missing theorem from a
clean build or infer Eq. (9) from Theorem 4.

## Exact source crosswalk

All new declarations use namespace `Reconstruction.LayoutMismatch.PublishedFiltration`.

| Printed location | Exact local theorem(s) | Mathematical coverage |
| --- | --- | --- |
| [Lines 418–450](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/papers/paper_polynomial_recovery.tex#L418-L450) | `published_basis_dual`, `publishedBasisEquiv`, `basis_entry_half_split` | Actual tensor-coordinate basis from the published local vectors and dual masks; one half-slot determines input vectors in the group low subspace. |
| [Lines 452–459, 505–507](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/papers/paper_polynomial_recovery.tex#L452-L459) | `mem_Hlt`, `mem_Ilt`, `Hlt_zero`, `Ilt_zero`, `filtrationCoordinates`, `Hlt_finrank`, `Hlt_dim_increment` | Ordinary rational polynomial coordinates with monic factors `rootProduct`, actual degree cutoff and all nodal equations. `Hlt n` and `Ilt n` mean degree < n; `n=j+1` is the printed level, and `n=0` is the minus-one level. |
| [Equation (9), lines 462–473](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/papers/paper_polynomial_recovery.tex#L462-L473) | `tensorAt_nodal_half_factor`, `exact_nodal_kernel_equiv`, `half_nodal_target_dimension`, `equation_nine`, `equation_nine_actual_incidence_axes` | Actual common tensor coordinates and actual clipped measurement blocks. Their half-mask target is the product of exactly those matrix ranges. Its dimension is exactly 2^(#T−1) times the sum of their ranks. Rank-nullity gives the codimension inequality, not equality of the combined constraint rank. The indexed corollary has the original node and variable subsets, chooses each output factor, and does not clip away any measurement rows. |
| [Lines 476–493](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/papers/paper_polynomial_recovery.tex#L476-L493) | `nodal_test_annihilates_allowed_tensor`, `read_tensor_coordinate_at_origin`, `forced_origin_coordinate_zero`, `beyond_degree_origin_zero` | For the actual `I_j`, the polynomial test annihilates every node and hence yields zero in the claimed origin coordinate. Its B-root factor is divided by its nonzero constant (the published Lean normalization). The degree bound is R+j+#B, and no gain beyond the strict root-count threshold is asserted. |
| [Lines 495–512](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/papers/paper_polynomial_recovery.tex#L495-L512) | `originKernelEquiv`, `origin_dim_increment`, `origin_increment_count`, `finite_codimension_lower_by_deleted`, `sum_deleted_is_literal_budget`, `displayed_filtration_mismatch_budget` | Multiplication by `X` gives the actual linear kernel isomorphism. Division preserves both the monic coordinate divisibility and the actual nodal checks. The image injects into the surviving origin coordinates. Exact counts telescope to the displayed positive-part budget. |
| [Equation (7), lines 406–416 and 515–518](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/papers/paper_polynomial_recovery.tex#L515-L518) | `mismatch_rank_selected_via_filtration`, `mismatch_rank_via_filtration` | The accepted baseline weighted count converts the literal dimension proof into the same normalized mismatch-rank inequality, including restriction from original incidence rows to the selected variables and nodes. |

The standalone Eq. (9) needs only nonempty selected nodes to express the
half-dimension by `2^(#T)/2`; it does not need distinctness or
nonzeroness. The subsequent polynomial test uses distinct and nonzero
nodes, the true identity constant matrix, the original nominal degree
bound, and the actual node-dependent foreign-group row span condition.
No additional regularity of the layout is imposed.

## A.2 construction and cost

[Proposition A.2, lines 688–709](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/papers/paper_polynomial_recovery.tex#L688-L709)
asserts parsimonious extension, a linear count of added variables and
clauses, the bounded-occurrence/width bookkeeping, and linear time when the
graph is already supplied; it explicitly does not generate the expander.

The existing Lean module [`ExpansionGraphCost.lean`](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/formal/ExpansionGraphCost.lean#L4-L19)
sets the cost unit to records/word operations. The openable source
[`ExpansionGraphCostConformance.lean`](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/blob/95ad3fb52aeac8376ba835b76987ef5f9d6156d6/reconstruction-studies/formal/ExpansionGraphCostConformance.lean#L106-L136)
then proves `constructFromEdges_linear_parsimonious` and
`constructFromEdges_degree_three_bound` for the supplied valid edge list.
No new proof is needed to cover that exact record model. The bare phrase
“linear time” should not be read as `O(n+m)` (where `m` is the number of edges) Turing-bit time: in a
literal binary clause encoding, just writing the three occurrences of each
fresh variable with index at least `n` already uses
`Ω(m log(n+1))` bits. This is not a statement about compressed
output or an uncharged expander construction. No bit-time theorem is
claimed by this overlay.

## Replay

Run `replay_paper2_overlay.py` in Python 3, passing
`--published-formal <published checkout>/reconstruction-studies/formal`,
`--lean <path to pinned Lean 4.24.0>`, and
`--out <fresh writable result directory>`. The script checks the exact
compiler commit and Lake Mathlib revision. It checks the SHA-256 of every
used original module against the public source manifest, excludes old
project objects, and builds all selected sources serially. Only pinned
Mathlib and transitive third-party build objects are reused. The summary
reports original and overlay rows separately, including exact source,
object and log SHA-256 values and the axiom sets. An original source
without an internal `#print axioms` still must compile; checked overlay
exports list their allowed standard dependencies explicitly.

