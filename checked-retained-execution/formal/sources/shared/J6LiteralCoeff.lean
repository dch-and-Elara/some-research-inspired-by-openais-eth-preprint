import J6PacketCoefficientBridge

namespace J6LiteralCoeff
open scoped Classical BigOperators
open MvPolynomial J6ActiveAllocation J6ActiveProfile J6FixedProfile J6BlockFactor
open J6PacketCoefficientBridge

variable {R I M K : Type*} [CommRing R] [Fintype I] [Fintype M]

noncomputable def profileFinsupp (b : M → Fin (Fintype.card I+1)) : M →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun m => (b m).val)

theorem target_coefficient_is_polynomial
    (w : M → ℕ) (f : I → Option M → R)
    (block : I → K) (target : M → K) (b : M → Fin (Fintype.card I+1))
    (k : K) (hzero : ∀ i m, block i ≠ target m → f i (some m) = 0) :
    targetCoeff w f block target b k =
      coeff ((profileFinsupp b).filter (fun m => target m = k))
        (∏ i : rows block k, ∑ v : Option M, monomial (exponent v) (scaled w f i.val v)) := by
  classical
  rw [coeff_allocations]
  unfold targetCoeff
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have outside (m : M) (hm : target m ≠ k) :
      ((profileFinsupp b).filter (fun m => target m = k)) m = 0 := by
    simp [hm]
  have inside (m : M) (hm : target m = k) :
      ((profileFinsupp b).filter (fun m => target m = k)) m = (b m).val := by
    simp [hm,profileFinsupp]
  by_cases hl : ∀ i m, y i = some m → k = target m
  · have hcount (m : M) (hm : target m ≠ k) : count y m = 0 := by
      unfold count
      have hfilter : (Finset.univ.filter (fun i => y i = some m)) = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => ?_)
        exact hm (hl i m (Finset.mem_filter.mp hi).2).symm
      simp [hfilter]
    have he : test block target b k y ↔
        ∀ m, count y m = ((profileFinsupp b).filter (fun m => target m = k)) m := by
      constructor
      · intro ht m
        by_cases hm : target m = k
        · rw [inside m hm]
          exact ht.2 ⟨m,hm⟩
        · rw [outside m hm, hcount m hm]
      · intro h
        refine ⟨hl, ?_⟩
        intro m
        have hh := h m.val
        rwa [inside m.val m.property] at hh
    simp only [he]
  · have hz : (∏ i : rows block k, scaled w f i.val (y i)) = 0 := by
      push_neg at hl
      obtain ⟨i,m,hy,ht⟩ := hl
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hy,scaled,hzero i.val m (i.property.trans_ne ht),mul_zero]
    have ht : ¬ test block target b k y := fun h => hl h.1
    rw [if_neg ht]
    split <;> simp_all only

#print axioms target_coefficient_is_polynomial

omit [Fintype I] in
theorem source_signed_row (bit : Bool) (base : R) (cross : M → R) :
    (∑ v : Option M, monomial (exponent v) (v.elim' (LiteralPortCompiler.affine bit base)
      (fun m => LiteralPortCompiler.slope bit * cross m))) =
      J6RecursiveModes.row bit base cross := by
  classical
  rw [Fintype.sum_option]
  rfl

#print axioms source_signed_row

end J6LiteralCoeff
