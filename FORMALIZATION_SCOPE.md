# Theorem index

All declarations below are in the namespace `LocalReconstruction`. The release paper uses the numbering of the v0.2 manuscript. The arguments of the polynomial matrix in the original problem have labels 1 through q, and all matrix coefficients are rational.

| Paper result | Lean declaration | Source |
|---|---|---|
| Walsh orthogonality and basis | `walsh_orthogonal`, `walshBasis` | [Walsh](BooleanCube/Walsh.lean) |
| Classification of bit-flip-invariant spaces | `flipInvariant_iff` | [Invariant](BooleanCube/Invariant.lean) |
| Equivalence of matrix conditions and edge constraints | `matrix_iff_edges` | [Reduction](BooleanCube/Reduction.lean) |
| Exact symmetric optimum, Theorem A | `symmetric_exact_integer_budget`, `symmetric_exact_real_budget` | [Budget](BooleanCube/Budget.lean), [RealBudget](BooleanCube/RealBudget.lean) |
| Dimension of the auxiliary space, (17) | `spline_dimension` | [Splines](BooleanCube/Splines.lean) |
| Square and bilinear certificates, (19), (23), (24) | `square_budget`, `bilinear_budget`, `bilinear_certificate` | [Certificates](BooleanCube/Certificates.lean), [BilinearBudget](BooleanCube/BilinearBudget.lean) |
| Uniform local binomial estimate, (10) | `uniform_local_binomial` | [Binomial](BooleanCube/Binomial.lean) |
| Weighted binomial-tail asymptotic, (21) | `weighted_binomial_asymptotic` | [Moderate](BooleanCube/Moderate.lean) |
| Sharp symmetric expansion, Theorem B | `symmetric_degree_asymptotic` | [Symmetric](BooleanCube/Symmetric.lean) |
| General leading-order optimum, Theorem C | `asymmetric_degree_asymptotic` | [AsymmetricResults](BooleanCube/AsymmetricResults.lean) |
| General second-order lower and upper bounds, (5) | `asymmetric_second_order_bounds` | [AsymmetricResults](BooleanCube/AsymmetricResults.lean) |

The minima are taken over the matrix schemes in Section 1. The [symmetric degree](BooleanCube/SymmetricDegree.lean) and the [degree with bit flips alone](BooleanCube/Asymmetric.lean) each have an attainment proof. In Theorem A every retained interval lies in the integer range from 0 through q. This makes explicit the domain implicit in the manuscript's equivalent gap formula. For the finite real-budget identity, Lean quantifies over all real γ. Theorems B, C and (5) quantify over each fixed real γ greater than 1/2.
