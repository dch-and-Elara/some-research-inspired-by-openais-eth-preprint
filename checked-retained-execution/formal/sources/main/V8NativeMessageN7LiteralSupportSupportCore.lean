import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The common-sign support argument separated from the physical
tables.  Only a column witness supporting all local factors is used;
no positivity is claimed for an arbitrary deformed source. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
noncomputable section

variable {I Y : Type} [Fintype I] [Fintype Y]

def signedSum (keep : Y→Bool) (r : I→Y→ℚ) : ℚ :=
  ∑ y,if keep y then ∏ i,r i y else 0

omit [Fintype Y] in
theorem equality_active_factor_positive [Nonempty I] (z : I→ℚ) (nonpos : ∀ i,z i≤0) :
    0<(∏ i,(1-z i))+(∏ i,z i) := by
  have absProd : |∏ i,z i| = ∏ i,|z i| := Finset.abs_prod _ _
  have bound : (∏ i,|z i|) < (∏ i,(1-z i)) := by
    have lo : (∏ i,|z i|) ≤ (∏ i,(|z i|+(1/2:ℚ))) :=
      Finset.prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>by linarith)
    refine lo.trans_lt ?_
    refine Finset.prod_lt_prod_of_nonempty (fun i _=>by positivity) ?_ Finset.univ_nonempty
    intro i _
    rw [abs_of_nonpos (nonpos i)]
    linarith
  linarith only [absProd,bound,neg_le_abs (∏ i,z i)]

theorem common_phase_support (keep : Y→Bool) (r : I→Y→ℚ) (sign : I→ℚ)
    (unit : ∀ i, sign i = 1 ∨ sign i = -1)
    (nonneg : ∀ i y,0≤sign i*r i y) :
    signedSum keep r≠0 ↔ ∃ y,keep y=true ∧ ∀ i,r i y≠0 := by
  have mul : (∏ i,sign i)*signedSum keep r =
      ∑ y,if keep y then ∏ i,sign i*r i y else 0 := by
    unfold signedSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _=>?_
    cases keep y <;> simp [Finset.prod_mul_distrib]
  constructor
  · intro nz
    by_contra! n
    apply nz
    unfold signedSum
    apply Finset.sum_eq_zero
    intro y _
    by_cases h : keep y=true
    · obtain ⟨i,z⟩ := n y h
      rw [if_pos h,Finset.prod_eq_zero (Finset.mem_univ i) z]
    · rw [if_neg h]
  · rintro ⟨y,hy,rows⟩ z
    have pos : 0 < (∏ i,sign i)*signedSum keep r := by
      rw [mul]
      apply Finset.sum_pos'
      · intro v _
        split
        · exact Finset.prod_nonneg fun i _=>nonneg i v
        · rfl
      · refine ⟨y,Finset.mem_univ y,?_⟩
        rw [if_pos hy]
        apply Finset.prod_pos
        intro i _
        apply lt_of_le_of_ne (nonneg i y)
        symm
        exact mul_ne_zero (by rcases unit i with h|h <;> rw [h] <;> norm_num) (rows i)
    exact (ne_of_gt pos) (by rw [z,mul_zero])

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.equality_active_factor_positive
#print axioms V8NativeMessage.N7LiteralSupport.common_phase_support
