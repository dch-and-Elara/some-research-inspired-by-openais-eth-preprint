import GrenetRankComplete

open Matrix GrenetMcCoy Round4Prefix Round4Transfer

namespace GrenetPaper

/-- Concrete all-support certificate using the proved normalized half-block. -/
theorem four_t_full_minor {K : Type*} [Field K] (q : ℚ →+* K) (t : ℕ) (E : Finset ℕ)
    (hcard : E.card = 2 * t) (z : K) :
    ∃ rows : E → Fin (4 * t),
      ((evaluationMatrix (fun i => z + (i.val : K)) E).submatrix rows id).det ≠ 0 :=
  GrenetRankComplete.finset_full_minor q t E hcard z

/-- The uniform upper bound under the original ring and step conditions. -/
theorem four_t_samples {R : Type*} [CommRing R] [IsAddTorsionFree R]
    (t : ℕ) (a b : R) (hb : b ∈ nonZeroDivisors R) :
    DeterminesUnboundedSparse (progression (prefixOffsets t) a b) t :=
  four_t_samples_of_no_common_root t a b hb
    (algebraMap ℚ (AlgebraicClosure ℚ))
    (fun E h z => four_t_full_minor (algebraMap ℚ (AlgebraicClosure ℚ)) t E h z)

end GrenetPaper
