# Paper 6 theorem index

[Paper 6 PDF](paper/Paper6.pdf) · [LaTeX source](paper/Paper6.tex) · [Historical evidence catalogue](paper/EVIDENCE_CATALOG.md)

Section and page numbers refer to the 105-page edition. Appendix E and Appendix K retain the v8 and v9 declaration maps at their historical scope. Section 18 summarizes those maps and points to the R119 results below.

## R119 endpoints

| Passage | Lean declarations | Scope |
| --- | --- | --- |
| J2, §16.2 and Appendix M.1, pp. 65–66, 102 | `J2R119Probability.words_expected`, `J2R119Probability.complete_words_expected`, `J2R119Probability.words_expected_sup` | The finite paired promise, adaptive decision trees indexed by an arbitrary probability space, almost-everywhere measurable paid query count, and a null-measurable success event on each input. With success at least 2/3 on each input, the supremum of the expectations is at least 2^d/72 under the stated support and free-reply conditions. |
| J2, native grouped and complete-only interfaces, Appendix M.1, p. 102 | `J2R119Probability.actual_grouped_probability`, `J2R119Probability.actual_complete_only_probability`, `J2R119Probability.actual_J2_published_expected_probability` | The individual applications take the actual low-precision completed D-menu erasure as a premise. Under the joint theorem's printed source, packing and MAIN hypotheses, one selected D packing certifies erasure and supports both native guarantees. The exponents use the grouped hit floor and the full private-word length, respectively. The bounds count paid queries. |
| J6, source entrance, §16.6 and Appendix O, pp. 68–69, 104–105 | `Paper6SourceSize.padded_size_eq`, `Paper6SourceSize.sourceInitialPrecision_eq`, `J6R52FreshShape.generated_fresh_root_uses_literal_source_cutoff`, `J6R114PrescribedReceipts.literal_source_startup_emits_the_padded_source_ordinal` | The cutoff uses the padded variable-plus-clause count and the factor-width parameter is the subdivision count. The actual startup emits the padded variable count plus one, with the execution specialized to truncation order one. |
| J6, group preparation and retained exterior, Appendix O, pp. 104–105 | `J6R114PrescribedReceipts.fresh_posted_and_mounted_payload_has_literal_source_scale`, `J6R117RetainedExteriorClock.actual_prescribed_exterior_clock_with_real_first_and_retained_subtrees` | The real posted row supplies the size and selector under the source correspondence. The exterior bound uses the actual first child and retained suffix, with separate stopped and active cases. The prescribed last point uses the absolute-depth certificate. |
| J6, prescribed-order count and clock, Appendix O, pp. 104–105 | `J6R114PrescribedReceipts.literal_source_run_counts_and_pays_the_same_clock` | Both the exact original-CNF model count and the step bound concern the same returned meter. The typed startup and group plan, ordered-byte equality, mounted preparation cap and root-contraction certificates are hypotheses. The preparation meter includes actual chart generation and mount, plus four wrapper steps. |
| J6, named workspace, Appendix O, p. 104 | `J6R114PrescribedReceipts.posted_row_workspace_uses_source_size`, `J6R116RetainedExteriorPeak.actual_paid_chart_and_retained_exterior_path_take_one_named_maximum` | At a posted group, the bound takes the maximum of the chart-build, pre-child and reached-path entry peaks. The chart-build cut and entry and suspended-frame bounds are hypotheses. The mounted chart is shared along the group path, with named ambient data included. General heap use and reclamation are outside the statement. |
| J6, binary probe order, Appendix O, p. 105 | `Paper6CanonicalChosenInstance.actual_chosen_order_is_the_metered_prefix`, `Paper6CanonicalChosenInstance.the_paid_table_matches_every_actual_chosen_prefix`, `J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts`, `J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts_and_time` | The binary-order instance proves the legal paid table matches its own ordered prefix. Exact count and time use the same binary run at the literal source precision and order one, with its typed inputs and preparation and root contracts. The table equality is internal to this choice of probe order. |

The J6 clock is an upper bound in the stated metered execution. Constructing arbitrary supplied inputs from raw bytes and evaluating arbitrary completed-slot oracles are outside its scope.

## Other source correspondences

| Passage | Lean declarations | Scope |
| --- | --- | --- |
| J2 zero probe, Appendix M.2, p. 102 | `J2R47P9ZeroProbe.source_native_full_zero_from_OR_cutoff`, `J2R47P9ZeroProbe.original_exterior_tied_layout_with_full_zero` | The strict row-coverage cutoff for a given layout and existence of a single certified layout for all active centers are distinct. A zero-probe value is delivered only if the installed list includes zero. |
| F5, §7.5 and Appendix N.3, pp. 29–30, 103 | `F5R62.PhysicalEmit.final_emitted_cnf_decides_original_sat`, `F5R63.Sparsify.actual_ambient_F5_large_original_source_dispatch` | SAT decision equivalence for the emitted CNF and the two printed source entrances under the stated hypotheses. Linear size counts vertices, edges and literal occurrences. The binary length is bounded separately. |
| J3, §16.3 and Appendix N.1, pp. 66, 103 | `J3R38LiteralSingleton.actual_constant_is_Ht`, `J3R38LiteralSingleton.original_J3_equation` | Read the zeroth and first coefficients of the same requested jet. The constant coefficient can depend on the private signs. |
| J8, §14.3 and Appendix N.2, pp. 54–55, 103 | `J8R59.literal_same_center_anchored_singleton`, `J8R64.actual_all_pins_from_every_full_precision_roster`, `J9FactorBounds.rowDiff_formula`, `J9FactorBounds.cleared_exact_odd` | The public anchor and mode depend on the layout and moment order. The request count is indexed. The equality-row derivative is integral and the specified odd product clears the kernel slope denominators. |

## Verification receipt

The final R119 check used Lean 4.24.0 and Mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. It recompiled the corrected modules listed below, verified the reused artifacts against their prior sources, objects and receipts, and ran each route's endpoint list in Lean.

| Route | Verified modules | Reused after verification | Recompiled in final run | Module axiom reports | Endpoint axiom reports |
| --- | ---: | ---: | --- | ---: | ---: |
| Main | 3,136 | 3,135 | `Paper6R119LiteralSourceRun` | 11,810 | 36 |
| Binary | 1,483 | 1,481 | `CanonicalFreshPhysicalTime`, `Paper6R119LiteralSourceRun` | 5,505 | 35 |

The endpoint reports use only `propext`, `Classical.choice` and `Quot.sound`, when needed. The report totals count requests for axiom dependencies, including repeated declarations across routes and across the module and endpoint lists. The final check was incremental on both routes. The binary audit also ran two checks that the count and step projections come from the same meter. In the main route the count-and-clock theorem itself states both conclusions for one meter.
