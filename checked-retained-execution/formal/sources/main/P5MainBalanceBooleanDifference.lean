import P5MainBalancePatchSupport

/-! Literal Boolean finite differences for the order-j source patch,
including the exact Taylor pair restriction. No general-rank or
separation premise is used in this coefficient identity. -/
namespace P5MainBalance
open Polynomial
open scoped BigOperators Classical

variable {W R K : Type*} [DecidableEq W] [CommRing R]

def boolSet (S : Finset W) (v : W) : Bool := decide (v∈S)

def subsetIndicator (A U : Finset W) : R := if A⊆U then 1 else 0

def boolDifference (S : Finset W) (F : Finset W→R) : R :=
  ∑ U∈S.powerset,(-1:R)^((S \ U).card)*F U

theorem alternating_powerset (S : Finset W) :
    (∑ U∈S.powerset,(-1:R)^U.card) = if S=∅ then 1 else 0 := by
  calc
    _ = ∏ _w∈S,((-1:R)+1) := by rw [Finset.prod_add]; simp
    _ = _ := by
      by_cases h : S=∅
      · simp [h]
      · simp [h,Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr h)]

private theorem sdiff_powerset_sum (A S : Finset W) (hA : A⊆S) :
    (∑ U∈S.powerset.filter (fun U=>A⊆U),(-1:R)^(S\U).card) =
      ∑ T∈(S\A).powerset,(-1:R)^T.card := by
  refine Finset.sum_bij (fun U _=>S\U) ?_ ?_ ?_ ?_
  · intro U hU
    have hu := (Finset.mem_filter.mp hU).2
    apply Finset.mem_powerset.mpr
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1,fun h=> (Finset.mem_sdiff.mp hv).2 (hu h)⟩
  · intro U hU U' hU' he
    have h := congrArg (fun X=>S\X) he
    change S \ (S \ U) = S \ (S \ U') at h
    rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1),
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (Finset.mem_filter.mp hU').1)] at h
    exact h
  · intro T hT
    have ht := Finset.mem_powerset.mp hT
    have hu : A⊆S\T := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨hA hv,fun h=> (Finset.mem_sdiff.mp (ht h)).2 hv⟩
    exact ⟨S\T,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset,hu⟩,
      Finset.sdiff_sdiff_eq_self (ht.trans Finset.sdiff_subset)⟩
  · intro U _
    rfl

theorem boolDifference_indicator (A S : Finset W) :
    boolDifference S (subsetIndicator (R:=R) A)=if A=S then 1 else 0 := by
  by_cases hA : A⊆S
  · unfold boolDifference subsetIndicator
    simp_rw [mul_ite,mul_one,mul_zero]
    rw [←Finset.sum_filter,sdiff_powerset_sum A S hA,alternating_powerset]
    have h : S\A=∅ ↔ A=S :=
      ⟨fun he=>Finset.Subset.antisymm hA (Finset.sdiff_eq_empty_iff_subset.mp he),
       fun he=>by subst S; simp⟩
    simp only [h]
  · have hne : A≠S := fun he=>hA he.le
    rw [if_neg hne]
    unfold boolDifference subsetIndicator
    exact Finset.sum_eq_zero (fun U hU => by rw [if_neg (fun h=>hA (h.trans (Finset.mem_powerset.mp hU))),mul_zero])

theorem boolDifference_finite_monomials (J : Finset K) (supp : K→Finset W)
    (c : K→R) (S : Finset W) :
    boolDifference S (fun U => ∑ a∈J,c a * subsetIndicator (supp a) U) =
      ∑ a∈J,if supp a=S then c a else 0 := by
  unfold boolDifference
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = c a * boolDifference S (subsetIndicator (supp a)) := by
      unfold boolDifference
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U _
      ring
    _ = _ := by rw [boolDifference_indicator]; split <;> simp

theorem reconstruct_small_support (q : ℕ) (J : Finset K) (supp : K→Finset W)
    (c : K→R) (hc : ∀ a∈J,(supp a).card≤q)
    (F : Finset W→R) (hF : ∀ U,F U=∑ a∈J,c a*subsetIndicator (supp a) U)
    (X : Finset W) :
    F X = ∑ S∈X.powerset.filter (fun S=>S.card≤q),boolDifference S F := by
  have hfun : F = fun U=>∑ a∈J,c a*subsetIndicator (supp a) U := funext hF
  conv_rhs => rw [hfun]
  simp_rw [boolDifference_finite_monomials]
  rw [Finset.sum_comm,hF]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hh : supp a⊆X
  · have hm : supp a∈X.powerset.filter (fun S=>S.card≤q) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hh,hc a ha⟩
    rw [Finset.sum_eq_single_of_mem (supp a) hm (fun w _ hw=>if_neg (Ne.symm hw))]
    simp [subsetIndicator,hh]
  · unfold subsetIndicator
    rw [if_neg hh,mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro w hw
    have hs := Finset.mem_powerset.mp (Finset.mem_filter.mp hw).1
    have hne : supp a≠w := by
      intro he
      exact hh (by simpa only [he] using hs)
    exact if_neg hne

/-- Actual source patch degree j permits exactly the Boolean-difference
window used in the manuscript. The order j extraction is before the
sum over Boolean assignments; that finite sum commutes with the formula. -/
theorem patch_eval_by_small_pairs {E : Type*} [Fintype E]
    (owner : E→W) (base delta : E→R[X]) (j : ℕ) (X : Finset W) :
    (patchProduct owner base delta (boolSet X)).coeff j =
      ∑ S∈X.powerset.filter (fun S=>S.card≤j),
        ∑ U∈S.powerset,(-1:R)^((S\U).card)*
           (patchProduct owner base delta (boolSet U)).coeff j := by
  let J : Finset (Finset E) := Finset.univ.powerset.filter (fun S=>S.card≤j)
  let A (S : Finset E) := @Finset.image E W (Classical.decEq W) owner S
  let c (S : Finset E) := (patchMonomial base delta S).coeff j
  have hF (Y : Finset W) :
      (patchProduct owner base delta (boolSet Y)).coeff j =
        ∑ S∈J,c S*subsetIndicator (A S) Y := by
    rw [actual_low_order_support]
    apply Finset.sum_congr rfl
    intro S _
    have H : (∀ w∈A S,boolSet Y w=true) ↔ A S⊆Y := by simp [boolSet,Finset.subset_iff,A]
    by_cases hv : A S⊆Y
    · rw [if_pos (H.mpr hv)]
      simp [subsetIndicator,hv,c]
    · rw [if_neg (fun h=>hv (H.mp h))]
      simp [subsetIndicator,hv]
  exact reconstruct_small_support j J A c
    (fun S h=>support_uses_at_most_order owner S j ((Finset.mem_filter.mp h).2)) _ hF X

#print axioms alternating_powerset
#print axioms boolDifference_indicator
#print axioms boolDifference_finite_monomials
#print axioms reconstruct_small_support
#print axioms patch_eval_by_small_pairs
end P5MainBalance
