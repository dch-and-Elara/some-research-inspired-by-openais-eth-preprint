import P5MainIteratorTrace
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators

/-! An actual anchored MAIN patch contributes an outer z whenever
its Boolean auxiliary flag is used. Expansion is over incidence subsets,
not over independently multilinearized factors. Repeated variables are
merged by image into a Boolean support. -/
namespace P5MainBalance
open Polynomial
open scoped BigOperators Classical

variable {R E W : Type*} [CommRing R] [Fintype E]

noncomputable def patchProduct (owner : E→W) (base delta : E→R[X]) (x : W→Bool) : R[X] :=
  ∏ e, ((if x (owner e) then X*delta e else 0)+base e)

noncomputable def patchMonomial (base delta : E→R[X]) (S : Finset E) : R[X] :=
  X^S.card * ((∏ e∈S,delta e)*(∏ e∈(Finset.univ \ S),base e))

theorem patch_selected_factor (owner : E→W) (delta : E→R[X]) (x : W→Bool)
    (S : Finset E) :
    (∏ e∈S,if x (owner e) then X*delta e else 0) =
      if ∀ e∈S,x (owner e)=true then X^S.card*(∏ e∈S,delta e) else 0 := by
  by_cases h : ∀ e∈S,x (owner e)=true
  · rw [if_pos h]
    rw [Finset.prod_congr rfl (fun e he => if_pos (h e he)),Finset.prod_mul_distrib,Finset.prod_const]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨e,he,hb⟩ := h
    exact Finset.prod_eq_zero he (by simp [hb])

theorem patch_exact_expansion (owner : E→W) (base delta : E→R[X]) (x : W→Bool) :
    patchProduct owner base delta x =
      ∑ S ∈ (Finset.univ : Finset E).powerset,
        if ∀ e∈S,x (owner e)=true then patchMonomial base delta S else 0 := by
  unfold patchProduct
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [patch_selected_factor]
  by_cases h : ∀ e∈S,x (owner e)=true <;> simp [h,patchMonomial,mul_assoc]

theorem patch_large_support_zero (base delta : E→R[X]) (S : Finset E)
    (j : ℕ) (hj : j<S.card) :
    (patchMonomial base delta S).coeff j=0 :=
  (X_pow_dvd_iff.mp ⟨_,rfl⟩) j hj

theorem actual_low_order_support (owner : E→W) (base delta : E→R[X]) (x : W→Bool) (j : ℕ) :
    (patchProduct owner base delta x).coeff j =
      ∑ S ∈ ((Finset.univ : Finset E).powerset.filter (fun S => S.card≤j)),
        if ∀ w∈S.image owner,x w=true then (patchMonomial base delta S).coeff j else 0 := by
  rw [patch_exact_expansion,finset_sum_coeff,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  have hV : (∀ w∈S.image owner,x w=true) ↔ (∀ e∈S,x (owner e)=true) := by
    constructor
    · intro h e he
      exact h _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)
    · intro h w hw
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hw
      exact h e he
  by_cases hx : ∀ e∈S,x (owner e)=true
  · have hx' := hV.mpr hx
    by_cases hj : S.card≤j
    · rw [if_pos hx,if_pos hj,if_pos hx']
    · rw [if_pos hx,if_neg hj,patch_large_support_zero base delta S j (by omega)]
  · have hx' := fun h => hx (hV.mp h)
    by_cases hj : S.card≤j
    · rw [if_neg hx,if_pos hj,if_neg hx',Polynomial.coeff_zero]
    · rw [if_neg hx,if_neg hj,Polynomial.coeff_zero]

omit [Fintype E] in
theorem support_uses_at_most_order (owner : E→W) (S : Finset E) (j : ℕ) (h : S.card≤j) :
    (S.image owner).card≤j := Finset.card_image_le.trans h

#print axioms patch_exact_expansion
#print axioms patch_large_support_zero
#print axioms actual_low_order_support
#print axioms support_uses_at_most_order
end P5MainBalance
