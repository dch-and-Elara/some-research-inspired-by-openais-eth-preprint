import Rational
import GrenetSameSign

open Polynomial Matrix GrenetMcCoy Round4Transfer

namespace GrenetPaper

variable {ι : Type*}

/-- Any k strictly same-sign samples certify recovery of up to t terms,
where k = 2t. The sample list may include other nodes. -/
theorem rational_determining_of_same_sign (x : ι → ℚ) (t : ℕ) (rows : Fin (2*t) → ι)
    (hx : Function.Injective (x ∘ rows))
    (hs : (∀ i, 0 < x (rows i)) ∨ (∀ i, x (rows i) < 0)) :
    DeterminesUnboundedSparse x t := by
  classical
  intro f g hf hg he
  let d := max f.natDegree g.natDegree + 2*t
  have hsize : min (2*t) (d+1) = 2*t := min_eq_left (by dsimp [d]; omega)
  have hdegree : DeterminesSparse x d t := by
    apply (determinesSparse_iff_max_support_matrices _ _ _).mpr
    intro E _ hc
    let en : E ≃ Fin (2*t) := E.equivFinOfCardEq (hc.trans hsize)
    let e (i : Fin (2*t)) : ℕ := (en.symm i).val
    let r (i : E) := rows (en i)
    let M := (evaluationMatrix x E).submatrix r id
    have hd := GrenetSameSign.det_pow_ne_zero_rat (x ∘ rows) e hx
      (Subtype.val_injective.comp en.symm.injective) hs
    have hM : M.submatrix en.symm en.symm = Matrix.of (fun i j => (x ∘ rows) i ^ e j) := by
      ext i j
      change x (rows (en (en.symm i))) ^ e j = x (rows i) ^ e j
      rw [en.apply_symm_apply]
    have hdet : M.det ≠ 0 := by rwa [← Matrix.det_submatrix_equiv_self en.symm M, hM]
    refine injective_of_fullMinorIdeal_eq_top _ (Ideal.eq_top_of_isUnit_mem _ ?_
      (isUnit_iff_ne_zero.mpr hdet))
    exact Ideal.subset_span ⟨r, rfl⟩
  exact hdegree f g ⟨by dsimp [d]; omega, hf⟩ ⟨by dsimp [d]; omega, hg⟩ he

end GrenetPaper
