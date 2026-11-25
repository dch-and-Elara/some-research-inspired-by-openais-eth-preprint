import LayoutBudget
import Mathlib.Tactic

namespace Reconstruction.LayoutMoments

open Finset
open scoped BigOperators
noncomputable section

/-- Number of mismatches on a specified node set for one candidate incidence. -/
def mismatchCount {I V G Factor : Type*} [DecidableEq G]
    (T : Finset I) (a : I → V → G) (b : I → Factor → G) (v : V) (f : Factor) : ℕ :=
  (T.filter (fun t => a t v ≠ b t f)).card

/-- Choose a maximizing factor separately for each variable and for this node set. -/
theorem exists_factor_selection {I V G Factor : Type*} [Fintype V] [DecidableEq G]
    (T : Finset I) (a : I → V → G) (b : I → Factor → G)
    (menu : V → Finset Factor) (δ : ℝ) (Δ : ℕ) (hΔ : 0 < Δ)
    (hne : ∀ v, (menu v).Nonempty) (hsize : ∀ v, (menu v).card ≤ Δ)
    (hdemand : ∀ t ∈ T, δ*(Fintype.card V : ℝ) ≤
      ∑ v, ∑ f ∈ menu v, if a t v ≠ b t f then (1:ℝ) else 0) :
    ∃ chosen : V → Factor, (∀ v, chosen v ∈ menu v) ∧
      (∀ v f, f ∈ menu v → mismatchCount T a b v f ≤ mismatchCount T a b v (chosen v)) ∧
      (δ/(Δ:ℝ))*(Fintype.card V : ℝ)*T.card ≤
        ∑ v, (mismatchCount T a b v (chosen v):ℝ) := by
  classical
  have best (v : V) := Finset.exists_max_image (menu v) (mismatchCount T a b v) (hne v)
  choose chosen hchosen hmax using best
  refine ⟨chosen, hchosen, hmax, ?_⟩
  have count_eq (v : V) (f : Factor) :
      (mismatchCount T a b v f : ℝ) = ∑ t ∈ T, if a t v ≠ b t f then (1:ℝ) else 0 := by
    rw [← sum_filter]
    simp [mismatchCount]
  have hdem : (T.card : ℝ)*(δ*(Fintype.card V : ℝ)) ≤
      ∑ v, ∑ f ∈ menu v, (mismatchCount T a b v f : ℝ) := calc
    _ = ∑ t ∈ T, δ*(Fintype.card V : ℝ) := by simp
    _ ≤ ∑ t ∈ T, ∑ v, ∑ f ∈ menu v, if a t v ≠ b t f then (1:ℝ) else 0 :=
      sum_le_sum hdemand
    _ = _ := by
      rw [sum_comm]
      simp_rw [count_eq]
      apply sum_congr rfl
      intro v _
      exact sum_comm
  have hb : (∑ v, ∑ f ∈ menu v, (mismatchCount T a b v f : ℝ)) ≤
      (Δ:ℝ)*∑ v, (mismatchCount T a b v (chosen v):ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro v _
    calc
      _ ≤ ∑ _f ∈ menu v, (mismatchCount T a b v (chosen v):ℝ) :=
        sum_le_sum (fun f hf => by exact_mod_cast hmax v f hf)
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsize v) (Nat.cast_nonneg _)
  have hΔr : 0 < (Δ:ℝ) := by exact_mod_cast hΔ
  calc
    _ = ((T.card : ℝ)*(δ*(Fintype.card V : ℝ)))/(Δ:ℝ) := by ring
    _ ≤ _ := (div_le_iff₀ hΔr).mpr (by simpa only [mul_comm (Δ:ℝ)] using hdem.trans hb)

/-- The number of variables with at least half the prescribed mean is at least βn/2. -/
theorem heavy_mismatch_count {V : Type*} [Fintype V] (h : V → ℕ) (k : ℕ) (hk : 0 < k)
    (β : ℝ) (hβ : 0 ≤ β) (hmax : ∀ v, h v ≤ k)
    (hmean : β*(Fintype.card V : ℝ)*k ≤ ∑ v, (h v : ℝ)) :
    β*(Fintype.card V : ℝ)/2 ≤
      ((univ.filter fun v => β*(k:ℝ)/2 ≤ h v).card : ℝ) := by
  classical
  let A := univ.filter (fun v => β*(k:ℝ)/2 ≤ h v)
  have hg (v : V) : (h v : ℝ) ≤ (if β*(k:ℝ)/2 ≤ h v then (k:ℝ) else 0) + β*k/2 := by
    split_ifs with hv
    · exact (by exact_mod_cast hmax v : (h v:ℝ) ≤ k).trans (le_add_of_nonneg_right (by positivity))
    · simpa using (lt_of_not_ge hv).le
  have hsum := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hg v)
  rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, card_univ, nsmul_eq_mul,
    nsmul_eq_mul] at hsum
  change (∑ v, (h v:ℝ)) ≤ (A.card:ℝ)*k + (Fintype.card V:ℝ)*(β*k/2) at hsum
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  apply le_of_mul_le_mul_right _ hk0
  linarith only [hmean, hsum]

/-- If every k-node set has average at least B, at least Q-k+1 of the Q nodes
individually have value at least B. -/
theorem many_individual_nodes {I : Type*} [DecidableEq I] (nodes : Finset I)
    (m : I → ℝ) (B : ℝ) (k : ℕ) (hk : 0 < k) (hQ : k ≤ nodes.card)
    (havg : ∀ T ⊆ nodes, T.card = k → B ≤ (∑ t ∈ T, m t)/(k:ℝ)) :
    nodes.card-k+1 ≤ (nodes.filter fun t => B ≤ m t).card := by
  classical
  let bad := nodes.filter (fun t => ¬ B ≤ m t)
  have hn : bad.card < k := by
    by_contra! hbad
    obtain ⟨T, hT, hTk⟩ := Finset.exists_subset_card_eq hbad
    have hsub : T ⊆ nodes := hT.trans (filter_subset _ _)
    have hne : T.Nonempty := card_pos.mp (hTk ▸ hk)
    have hs := sum_lt_sum_of_nonempty hne (fun t ht =>
      lt_of_not_ge (mem_filter.mp (hT ht)).2)
    have havg' := (le_div_iff₀ (by exact_mod_cast hk : 0 < (k:ℝ))).mp (havg T hsub hTk)
    rw [sum_const, hTk, nsmul_eq_mul] at hs
    linarith only [hs, havg']
  let good := nodes.filter (fun t => B ≤ m t)
  have hd : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    exact (mem_filter.mp ht').2 (mem_filter.mp ht).2
  have hu : good ∪ bad = nodes := by
    ext t
    by_cases he : B ≤ m t
    · simp [good, bad, he]
    · simp [good, bad, he, lt_of_not_ge he]
  have hparts := Finset.card_union_of_disjoint hd
  rw [hu] at hparts
  change nodes.card - k + 1 ≤ good.card
  omega

end
end Reconstruction.LayoutMoments
