import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Literal nonzero-probe affine allocation and finite precision cut.
A repeated mode is charged for each row that selects it. -/
namespace J6ActiveAllocation
open scoped BigOperators
open scoped Classical
variable {R I M : Type*} [CommRing R] [Fintype I] [Fintype M]

def cost (w : M→ℕ) : Option M → ℕ :=
  Option.elim' 0 w

def total (w : M→ℕ) (x : I→Option M) : ℕ :=
  ∑ i, cost w (x i)

def scaled (w : M→ℕ) (f : I→Option M→R) (i : I) (x : Option M) : R :=
  (2:R)^(cost w x) * f i x

omit [Fintype M] in
theorem weighted_product (w : M→ℕ) (f : I→Option M→R) (x : I→Option M) :
    (∏ i, scaled w f i (x i)) = (2:R)^total w x * ∏ i, f i (x i) := by
  unfold scaled total
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

omit [Fintype M] in
theorem erased (w : M→ℕ) (f : I→Option M→R) (x : I→Option M)
    (p : ℕ) (hR : (2:R)^p=0) (hx : p ≤ total w x) :
    (∏ i, scaled w f i (x i)) = 0 := by
  rw [weighted_product, ← Nat.add_sub_of_le hx, pow_add,hR,zero_mul,zero_mul]

theorem truncated_expansion (w : M→ℕ) (f : I→Option M→R)
    (p : ℕ) (hR : (2:R)^p=0) :
    (∏ i, ∑ x : Option M, scaled w f i x) =
      ∑ x ∈ (Finset.univ : Finset (I→Option M)).filter (fun x=>total w x<p),
        ∏ i, scaled w f i (x i) := by
  classical
  rw [Fintype.prod_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : total w x<p
  · simp [h]
  · rw [if_neg h,erased w f x p hR (Nat.le_of_not_gt h)]

#print axioms weighted_product
#print axioms erased
#print axioms truncated_expansion
end J6ActiveAllocation