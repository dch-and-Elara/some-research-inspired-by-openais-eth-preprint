import GrenetRankArendt
import GrenetResidue
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open Matrix
open scoped BigOperators

namespace GrenetRankComplete

open GrenetResidue GrenetMcCoy Round4Transfer

/-- Full-prefix column rank for every starting point in any field receiving ℚ. -/
theorem ordered_full_minor {K : Type*} [Field K] (q : ℚ →+* K)
    (t : ℕ) (E : Fin (2*t) → ℕ) (hE : Function.Injective E) (z : K) :
    ∃ rows : Fin (2*t) → Fin (2*(2*t)),
      ((GrenetRank.prefixMatrix z E).submatrix rows id).det ≠ 0 :=
  GrenetRankArendt.ordered_full_minor_of_odd_part q t E hE z (normalized_odd_part t E hE)

/-- Full-minor statement in the Finset-indexed form used by the existing ring transfer. -/
theorem finset_full_minor {K : Type*} [Field K] (q : ℚ →+* K)
    (t : ℕ) (E : Finset ℕ) (hc : E.card = 2*t) (z : K) :
    ∃ rows : E → Fin (4*t),
      (Matrix.submatrix (evaluationMatrix (fun i : Fin (4*t) => z + (i.val : K)) E)
        rows id).det ≠ 0 := by
  classical
  let b : E ≃ Fin (2*t) := Fintype.equivOfCardEq (by simpa using hc)
  let e (i : Fin (2*t)) : ℕ := (b.symm i).val
  have he : Function.Injective e := Subtype.val_injective.comp b.symm.injective
  obtain ⟨rows, hrows⟩ := ordered_full_minor q t e he z
  let r (j : E) : Fin (4*t) := Fin.cast (by omega) (rows (b j))
  refine ⟨r, ?_⟩
  have hm : Matrix.submatrix (evaluationMatrix (fun i : Fin (4*t) => z + (i.val : K)) E)
        r id = ((GrenetRank.prefixMatrix z e).submatrix rows id).submatrix b b := by
    ext i j
    change (z + ((rows (b i)).val : K)) ^ j.val =
      (z + ((rows (b i)).val : K)) ^ (b.symm (b j)).val
    rw [b.symm_apply_apply]
  rw [hm, Matrix.det_submatrix_equiv_self]
  exact hrows

/-- The existing general-ring transfer now has a proved rank input. -/
theorem four_t_samples {R K : Type*} [CommRing R] [IsAddTorsionFree R]
    [Field K] [IsAlgClosed K] (q : ℚ →+* K)
    (t : ℕ) (a b : R) (hb : b ∈ nonZeroDivisors R) :
    DeterminesUnboundedSparse (Round4Transfer.progression (Round4Prefix.prefixOffsets t) a b) t :=
  Round4Prefix.four_t_samples_of_no_common_root t a b hb q (finset_full_minor q t)

/-- Choose the algebraic closure of ℚ internally for the original-ring endpoint. -/
theorem four_t_samples_unconditional {R : Type*} [CommRing R] [IsAddTorsionFree R]
    (t : ℕ) (a b : R) (hb : b ∈ nonZeroDivisors R) :
    DeterminesUnboundedSparse (Round4Transfer.progression (Round4Prefix.prefixOffsets t) a b) t :=
  four_t_samples (algebraMap ℚ (AlgebraicClosure ℚ)) t a b hb

end GrenetRankComplete
