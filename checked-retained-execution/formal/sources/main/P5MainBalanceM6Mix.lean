import P5MainBalanceM6Interval
import P5MainBalanceM6Swaps

/-! Direct proof for the original V₀ f(W₀), in the copied slot
basis used by the actual retained measurement rows. -/
namespace P5MainBalance.M6
open P5MainIterator Polynomial
open scoped BigOperators Classical

variable {Copy I B : Type*} [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

def outsideInterval (A R : ℕ) (j : ℕ) : Prop := ¬(A≤j ∧ j<A+R)

noncomputable def printedMix (A R : ℕ) : Operator Copy I B :=
  fullMatrix * Polynomial.aeval (weightMatrix : Operator Copy I B) (printedInterval A R)

private theorem pow_vector_eigen {S : Type*} [Fintype S] [DecidableEq S]
    (W : Matrix S S ℚ) (v : S→ℚ) (z : ℚ) (h : W.mulVec v=z•v) (n : ℕ) :
    (W^n).mulVec v=(z^n)•v := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ',←Matrix.mulVec_mulVec,hn,Matrix.mulVec_smul,h,smul_smul,pow_succ]

private theorem eval_vector_eigen {S : Type*} [Fintype S] [DecidableEq S]
    (W : Matrix S S ℚ) (v : S→ℚ) (z : ℚ) (h : W.mulVec v=z•v) (p : ℚ[X]) :
    (Polynomial.aeval W p).mulVec v=(p.eval z)•v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add,Matrix.add_mulVec,hp,hq,eval_add,add_smul]
  | monomial n c =>
    rw [Polynomial.aeval_monomial,←Matrix.mulVec_mulVec,pow_vector_eigen W v z h,
      Algebra.algebraMap_eq_smul_one,Matrix.smul_mulVec,Matrix.one_mulVec,
      smul_smul,eval_monomial]

set_option maxHeartbeats 11000000 in
theorem printedMix_exact_eigen (A R : ℕ) (r : SwapSlot Copy I B) :
    (printedMix A R : Operator Copy I B).mulVec (qOrbitRow CoordFamily r) =
      ((printedInterval A R).eval (boolWeight r.2:ℚ)*(-1:ℚ)^boolWeight r.2)•
      qOrbitRow CoordFamily r := by
  unfold printedMix
  rw [←Matrix.mulVec_mulVec,eval_vector_eigen _ _ _ (weight_eigen r),
    Matrix.mulVec_smul,full_eigen,smul_smul]

theorem printedMix_fixed_on_kept (A R : ℕ) (r : SwapSlot Copy I B)
    (h : A≤boolWeight r.2 ∧ boolWeight r.2<A+R) :
    (printedMix A R : Operator Copy I B).mulVec (qOrbitRow CoordFamily r)=qOrbitRow CoordFamily r := by
  rw [printedMix_exact_eigen,interval_eval_in_span A R (boolWeight r.2) h.1 h.2,
    ←mul_pow,show (-1:ℚ)*(-1)=1 by norm_num,one_pow,one_smul]

omit [Fintype Copy] [Fintype I] [Fintype B] in
theorem flipAt_literal_ordered_cell (i j : I) (s : SwapSlot Copy I B) :
    (copyDecode (flipAt i s)).2 j =
      if j=i then ((copyDecode s).2 j).swap else (copyDecode s).2 j := by
  by_cases he : j=i
  · subst j
    by_cases h : (s.1.2 i).val.1≠(s.1.2 i).val.2
    · unfold copyDecode decodeOrbit flipAt
      simp only [dif_pos h,ite_true]
      cases s.2 ⟨i,h⟩ <;> rfl
    · unfold copyDecode decodeOrbit flipAt
      simp only [dif_neg h,ite_true]
      exact Prod.ext (not_ne_iff.mp h) (not_ne_iff.mp h).symm
  · simp [copyDecode,decodeOrbit,flipAt,he]

omit [Fintype Copy] [Fintype I] [Fintype B] in
theorem flipAll_literal_ordered_cell (j : I) (s : SwapSlot Copy I B) :
    (copyDecode (flipAll s)).2 j=((copyDecode s).2 j).swap := by
  by_cases h : (s.1.2 j).val.1≠(s.1.2 j).val.2
  · unfold copyDecode decodeOrbit flipAll
    simp only [dif_pos h]
    cases s.2 ⟨j,h⟩ <;> rfl
  · unfold copyDecode decodeOrbit flipAll
    simp only [dif_neg h]
    exact Prod.ext (not_ne_iff.mp h) (not_ne_iff.mp h).symm

#print axioms printedMix_exact_eigen
#print axioms printedMix_fixed_on_kept
#print axioms flipAt_literal_ordered_cell
#print axioms flipAll_literal_ordered_cell
end P5MainBalance.M6
