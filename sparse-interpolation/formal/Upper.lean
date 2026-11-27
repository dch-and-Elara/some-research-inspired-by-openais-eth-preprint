import RingTransfer

open Matrix

namespace Round4Prefix

open GrenetMcCoy Round4Transfer

variable {R K : Type*}

def prefixOffsets (t : ℕ) (i : Fin (4 * t)) : ℕ := i.val

/-- Specialize the arbitrary-offset transfer to the first 4t points. -/
theorem four_t_samples_of_symbolic_unit_ideals [CommRing R] [IsAddTorsionFree R]
    (t : ℕ) (a b : R) (hb : b ∈ nonZeroDivisors R)
    (hE : ∀ E : Finset ℕ, E.card = 2 * t →
      fullMinorIdeal (symbolicMatrix (prefixOffsets t) E) = ⊤) :
    DeterminesUnboundedSparse (progression (prefixOffsets t) a b) t :=
  determinesUnboundedSparse_of_symbolic_unit_ideals (prefixOffsets t) a b hb t hE

/-- Pointwise nonzero full minor, in any algebraically closed extension
of Q, implies the uniform 4t bound in the original ring. -/
theorem four_t_samples_of_no_common_root [CommRing R] [IsAddTorsionFree R]
    [Field K] [IsAlgClosed K] (t : ℕ) (a b : R) (hb : b ∈ nonZeroDivisors R)
    (q : ℚ →+* K)
    (hE : ∀ (E : Finset ℕ), E.card = 2 * t → ∀ z : K, ∃ rows : E → Fin (4 * t),
      ((evaluationMatrix (fun i => z + (i.val : K)) E).submatrix rows id).det ≠ 0) :
    DeterminesUnboundedSparse (progression (prefixOffsets t) a b) t :=
  four_t_samples_of_symbolic_unit_ideals t a b hb fun E hc =>
    symbolic_fullMinorIdeal_eq_top_of_no_common_root (prefixOffsets t) E q (hE E hc)

/-- The equivalent pointwise injectivity input gives the same endpoint. -/
theorem four_t_samples_of_pointwise_injective [CommRing R] [IsAddTorsionFree R]
    [Field K] [IsAlgClosed K] (t : ℕ) (a b : R) (hb : b ∈ nonZeroDivisors R)
    (q : ℚ →+* K)
    (hE : ∀ (E : Finset ℕ), E.card = 2 * t → ∀ z : K,
      Function.Injective (evaluationMatrix (fun i : Fin (4 * t) => z + (i.val : K)) E).mulVec) :
    DeterminesUnboundedSparse (progression (prefixOffsets t) a b) t :=
  four_t_samples_of_symbolic_unit_ideals t a b hb fun E hc =>
    symbolic_fullMinorIdeal_eq_top_of_pointwise_injective (prefixOffsets t) E q (hE E hc)

end Round4Prefix
