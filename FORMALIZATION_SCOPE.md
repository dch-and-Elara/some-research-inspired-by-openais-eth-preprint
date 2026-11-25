# Theorem index

All declarations below are in the namespace `LocalReconstruction`. Sections 1–6 retain the original equation numbering. Section 7 gives the unrestricted matrix proof. The arguments of the polynomial matrix in the original problem have labels 1 through q, and all matrix coefficients are rational.

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
| Bit-flip leading-order optimum, Theorem C | `asymmetric_degree_asymptotic` | [AsymmetricResults](BooleanCube/AsymmetricResults.lean) |
| Bit-flip second-order bounds, (5) | `asymmetric_second_order_bounds` | [AsymmetricResults](BooleanCube/AsymmetricResults.lean) |
| Bilinear certificate (25) and square obstruction for arbitrary rational matrices | `matrix_bilinear_certificate`, `matrix_square_obstruction` | [MatrixCertificates](BooleanCube/MatrixCertificates.lean) |
| Finite row-count bounds (26) and (27) | `matrix_square_budget`, `matrix_bilinear_budget` | [TailReflection](BooleanCube/TailReflection.lean), [MatrixCertificates](BooleanCube/MatrixCertificates.lean) |
| Unrestricted matrix models and attainment | `unrestrictedScheme`, `unrestrictedDegree`, `unrestrictedDegree_feasible` | [Unrestricted](BooleanCube/Unrestricted.lean) |
| Unrestricted leading limit and second-order interval, (4) and (5) | `unrestricted_degree_asymptotic`, `unrestricted_second_order_bounds` | [AsymmetricResults](BooleanCube/AsymmetricResults.lean) |

Both unrestricted asymptotic theorems quantify over a Boolean parameter. The value `true` imposes ternary entries on the rational measurement matrix. The value `false` permits every rational entry. Both use the original `matrixCondition` and both allow arbitrary row spaces. The finite row-count theorems refer directly to an arbitrary rational matrix and allow distinct nonzero rational labels. In (26), the Lean sum runs through $k$, using the convention that a binomial coefficient vanishes above the dimension.

The minima are taken over the matrix schemes in Section 1. The [symmetric degree](BooleanCube/SymmetricDegree.lean) and the [degree with bit flips alone](BooleanCube/Asymmetric.lean) each have an attainment proof. In Theorem A every retained interval lies in the integer range from 0 through q. This makes explicit the domain implicit in the manuscript's equivalent gap formula. For the finite real-budget identity, Lean quantifies over all real γ. Theorems B, C and (5) quantify over each fixed real γ greater than 1/2.
