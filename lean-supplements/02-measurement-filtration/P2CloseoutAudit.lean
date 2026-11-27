import P2PublishedFiltrationConclude
import P2PublishedFiltrationSource
import VisitRuntime
import ExpansionGraphCostConformance
import ReleaseLayoutSigned
import ReleaseLayoutNumerical
import P2CloseoutLiteralLists

/-! Local closeout audit only: no replacement declaration or new theorem. -/
set_option autoImplicit false
set_option warningAsError true

-- §2 truthful quantities and three separately charged visits.
#print axioms Reconstruction.VisitRuntime.reachableImage_card_ge
#print axioms Reconstruction.VisitRuntime.Visits.rank_pow_le
#print axioms Reconstruction.VisitRuntime.Visits.taylor_sum_le
#print axioms Reconstruction.VisitRuntime.Visits.scan_pow_le

-- Theorems 1 and 3, and Corollary 2.
#print axioms Reconstruction.LayoutBudget.principal_subset_imbalance
#print axioms Reconstruction.normalized_nullity_budget
#print axioms Reconstruction.LayoutMoments.corollary_two
#print axioms Reconstruction.VisitRuntime.theorems3_and6_graph_family
#print axioms Reconstruction.VisitRuntime.theorem3_numerical
#print axioms Reconstruction.VisitRuntime.graph_preSubstitution_degree
#print axioms Reconstruction.VisitRuntime.theorem3_signed_graph_family

-- Theorem 4, and the published supplement following the literal proof.
#print axioms Reconstruction.LayoutMismatch.mismatch_rank
#print axioms Reconstruction.LayoutMismatch.phi_eq_positive_part
#print axioms Reconstruction.LayoutMismatch.PublishedFiltration.Hlt_dim_increment
#print axioms Reconstruction.LayoutMismatch.PublishedFiltration.equation_nine_actual_incidence_axes
#print axioms Reconstruction.LayoutMismatch.PublishedFiltration.originKernelEquiv
#print axioms Reconstruction.LayoutMismatch.PublishedFiltration.displayed_filtration_mismatch_budget
#print axioms Reconstruction.LayoutMismatch.PublishedFiltration.mismatch_rank_via_filtration

-- Corollary 5 and revised Theorem 6.
#print axioms Reconstruction.LayoutMoments.corollary_five
#print axioms Reconstruction.LayoutMoments.PublishedCandidateList.corollary_two_literal_lists
#print axioms Reconstruction.LayoutMoments.PublishedCandidateList.corollary_five_literal_lists
#print axioms Reconstruction.VisitRuntime.theorem6_numerical
#print axioms Reconstruction.VisitRuntime.unbalanced_from_candidates
#print axioms Reconstruction.VisitRuntime.paper_log_cost_conversion

-- Appendix A.1 and A.2: existence, exact geometry, and the supplied-list compiler.
#print axioms Reconstruction.ExpansionGraph.exists_expanding_graph
#print axioms Reconstruction.ExpansionGraph.exists_expanding_permutations
#print axioms Reconstruction.ExpansionGraph.replacement_balanced
#print axioms Reconstruction.VisitRuntime.paper_entropy_margin
#print axioms Reconstruction.ExpansionGraph.exists_parsimonious_expanding_extension
#print axioms Reconstruction.ExpansionGraph.gateExtension_width
#print axioms Reconstruction.ExpansionGraph.gateExtension_occurs_old
#print axioms Reconstruction.ExpansionGraph.gateExtension_occurs_new
#print axioms Reconstruction.ExpansionGraph.paddingCount_le
#print axioms Reconstruction.ExpansionGraph.paddingModelsEquiv
#print axioms Reconstruction.ExpansionGraph.constructFromEdges_linear_parsimonious
#print axioms Reconstruction.ExpansionGraph.constructFromEdges_degree_three_bound
#print axioms Reconstruction.VisitRuntime.parsimonious_extension_runtime

#check Reconstruction.VisitRuntime.PhysicalLayout.balanced
#check Reconstruction.VisitRuntime.Visits
#check Reconstruction.VisitRuntime.theorems3_and6_graph_family
#check Reconstruction.VisitRuntime.parsimonious_extension_runtime
#check Reconstruction.LayoutMismatch.PublishedFiltration.equation_nine_actual_incidence_axes
#check Reconstruction.LayoutMismatch.PublishedFiltration.mismatch_rank_via_filtration

