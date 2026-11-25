import LayoutMomentsHalf
import LayoutMomentsSelection

namespace Reconstruction.LayoutMoments

open Finset LayoutBudget Polynomial Matrix
open scoped BigOperators Classical Polynomial
noncomputable section

private theorem measurementRank_half_le {V G : Type*} [Fintype G] [DecidableEq G]
    {M : G → Type*} [∀ g, Fintype (M g)] (V₀ : Finset V) (U : Finset V₀)
    (a : V → G) (C : ∀ g, Matrix (M g) (GroupFiber a g) ℚ) :
    measurementRank (fun u : U => u.val.val) a C ≤
      measurementRank (fun v : V₀ => v.val) a C := by
  classical
  apply sum_le_sum
  intro g _
  let D := restrictGroupMatrix (fun v : V₀ => v.val) a g (C g)
  let F := restrictGroupMatrix (fun u : U => u.val.val) a g (C g)
  let e (u : GroupFiber (a ∘ (fun u : U => u.val.val)) g) :
      GroupFiber (a ∘ (fun v : V₀ => v.val)) g := ⟨u.val.val, u.property⟩
  have hr := Matrix.rank_submatrix_le e (Equiv.refl _) Dᵀ
  change Fᵀ.rank ≤ Dᵀ.rank at hr
  simpa only [Matrix.rank_transpose] using hr

private theorem cast_twiceImbalance {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
    (a b : V → G) :
    (twiceImbalance a b : ℝ) =
      ∑ g, |(Fintype.card (GroupFiber a g) : ℝ)-Fintype.card (GroupFiber b g)| := by
  simp only [twiceImbalance, Nat.cast_sum, Int.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast]

private theorem departures_le_source {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (a b : V → G) (g : G) : (departures a b g).card ≤ Fintype.card (GroupFiber a g) := by
  classical
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
    (fun v : departures a b g => (⟨v.val, (mem_filter.mp v.property).2.1⟩ : GroupFiber a g))
    (fun u v hu => Subtype.ext (congrArg (fun x : GroupFiber a g => x.val) hu))

private theorem sum_departures {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
    (a b : V → G) :
    (∑ g, ((departures a b g).card : ℝ)) =
      ∑ v, if a v ≠ b v then (1:ℝ) else 0 := by
  classical
  unfold departures
  simp_rw [← Finset.sum_boole]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [sum_eq_single (a v)]
  · simp [eq_comm]
  · intro g _ h
    simp [Ne.symm h]
  · simp

/-- Average of the doubled principal imbalance at one node, under a uniform group-size cap. -/
theorem expected_imbalance_ge_mismatches {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
    (a b : V → G) (gmax : ℕ) (hg : 0 < gmax)
    (hgroups : ∀ g, Fintype.card (GroupFiber a g) ≤ gmax) :
    (∑ v, if a v ≠ b v then (1:ℝ) else 0)/(24*Real.sqrt (2*(gmax:ℝ))) ≤
      𝔼 s : Bits V, (twiceImbalance (fun u : halfSet s => a u.val)
        (fun u : halfSet s => b u.val) : ℝ) := by
  simp_rw [cast_twiceImbalance]
  rw [expect_sum_comm, ← sum_departures a b, sum_div]
  apply sum_le_sum
  intro g _
  let x : ℝ := (departures a b g).card
  let y : ℝ := (arrivals a b g).card
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hxG : x ≤ (gmax:ℝ) := by
    dsimp [x]
    exact_mod_cast (departures_le_source a b g).trans (hgroups g)
  have hG : 0 < (gmax:ℝ) := by exact_mod_cast hg
  have hx2 : x^2 ≤ (x+y)*(gmax:ℝ) := by
    nlinarith only [mul_le_mul (show x ≤ x+y by linarith) hxG hx (by positivity)]
  have hs : x/Real.sqrt (2*(gmax:ℝ)) ≤ Real.sqrt ((x+y)/2) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hx2]
  have he := expect_abs_group_difference a b g
  push_cast at he
  change Real.sqrt ((x+y)/2)/24 ≤ _ at he
  rw [show x/(24*Real.sqrt (2*(gmax:ℝ))) = (x/Real.sqrt (2*(gmax:ℝ)))/24 by ring]
  exact (div_le_div_of_nonneg_right hs (by norm_num)).trans he

/-- Corollary 2 and equation (5) in the incidence model of the v2 paper. The
right side uses menu demand δ divided by the menu bound Δ. -/
theorem corollary_two {V I G Factor : Type*} [DecidableEq V]
    [Fintype G] [DecidableEq G] {M : I → G → Type*} [∀ t g, Fintype (M t g)]
    (V₀ : Finset V) (T : Finset I) (node : I → ℚ) (R : ℕ)
    (a : I → V → G) (b : I → Factor → G) (scope : Factor → V → Prop)
    (P : Factor → V → V → ℚ[X])
    (C : ∀ t g, Matrix (M t g) (GroupFiber (a t) g) ℚ)
    (menu : V₀ → Finset Factor) (δ : ℝ) (Δ gmax : ℕ)
    (hV : V₀.Nonempty) (hT : T.Nonempty)
    (hne : ∀ v, (menu v).Nonempty) (hsize : ∀ v, (menu v).card ≤ Δ)
    (hscope : ∀ v f, f ∈ menu v → scope f v.val)
    (hdemand : ∀ t ∈ T, δ*(V₀.card:ℝ) ≤
      ∑ v : V₀, ∑ f ∈ menu v, if a t v.val ≠ b t f then (1:ℝ) else 0)
    (hgroups : ∀ t ∈ T, ∀ g, Fintype.card (GroupFiber (fun v : V₀ => a t v.val) g) ≤ gmax)
    (hnodes : Set.InjOn node (↑T : Set I))
    (hzero : ∀ f v, scope f v → ∀ w, (P f v w).eval 0 = if v = w then 1 else 0)
    (hdegree : ∀ f v, scope f v → ∀ w, (P f v w).natDegree ≤ R)
    (hforeign : ∀ t ∈ T, ∀ f v, scope f v → ∀ g, b t f ≠ g →
      (fun w : GroupFiber (a t) g => (P f v w.val).eval (node t)) ∈
        Submodule.span ℚ (Set.range (C t g).row)) :
    (δ/(Δ:ℝ))*(V₀.card:ℝ)/(48*Real.sqrt (2*(gmax:ℝ))) ≤
      (∑ t : T, (measurementRank (fun v : V₀ => v.val) (a t) (C t):ℝ))/(T.card:ℝ) +
        (V₀.card:ℝ)*R/(2*(T.card:ℝ)) := by
  classical
  let a' (t : I) (v : V₀) := a t v.val
  have hΔ : 0 < Δ := by
    obtain ⟨v, hv⟩ := hV
    exact (card_pos.mpr (hne ⟨v,hv⟩)).trans_le (hsize ⟨v,hv⟩)
  have hg : 0 < gmax := by
    obtain ⟨v,hv⟩ := hV
    obtain ⟨t,ht⟩ := hT
    haveI : Nonempty (GroupFiber (a' t) (a t v)) := ⟨⟨⟨v,hv⟩, rfl⟩⟩
    exact Fintype.card_pos.trans_le (hgroups t ht (a t v))
  obtain ⟨chosen, hchosen, _, hselect⟩ := exists_factor_selection T a' b menu δ Δ hΔ hne hsize
    (by simpa only [Fintype.card_coe] using hdemand)
  rw [Fintype.card_coe] at hselect
  let b' (t : I) (v : V₀) := b t (chosen v)
  let imb (t : T) (s : Bits V₀) : ℝ :=
    twiceImbalance (fun u : halfSet s => a' t u.val) (fun u : halfSet s => b' t u.val)
  let m (t : T) : ℝ := measurementRank (fun v : V₀ => v.val) (a t) (C t)
  let D : ℝ := 24*Real.sqrt (2*(gmax:ℝ))
  have hD : 0 < D := by dsimp [D]; positivity
  have hQ : 0 < (T.card:ℝ) := by exact_mod_cast card_pos.mpr hT
  have hmatch : ((δ/(Δ:ℝ))*(V₀.card:ℝ)*T.card)/D ≤
      𝔼 s : Bits V₀, ∑ t : T, imb t s := by
    have hchange (v : V₀) : (mismatchCount T a' b v (chosen v):ℝ) =
        ∑ t : T, if a' t v ≠ b' t v then (1:ℝ) else 0 := by
      rw [T.sum_coe_sort (fun t : I => if a' t v ≠ b' t v then (1:ℝ) else 0)]
      rw [← sum_filter]
      simp [mismatchCount, b']
    simp_rw [hchange] at hselect
    rw [sum_comm] at hselect
    refine (div_le_div_of_nonneg_right hselect hD.le).trans ?_
    rw [sum_div, expect_sum_comm]
    exact sum_le_sum (fun t _ =>
      expected_imbalance_ge_mismatches (a' t) (b' t) gmax hg (hgroups t t.property))
  have hpr (s : Bits V₀) : (∑ t : T, imb t s) ≤
      2*((∑ t : T, m t)+(R:ℝ)*(halfSet s).card) := by
    have hh := principal_subset_imbalance V₀ (halfSet s) T node R a b scope chosen
      (fun v => hscope v (chosen v) (hchosen v)) P C hnodes hzero hdegree hforeign
    have hmono := sum_le_sum (fun t (_ : t ∈ (univ : Finset T)) =>
      measurementRank_half_le V₀ (halfSet s) (a t) (C t))
    have hb := hh.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hmono _))
    dsimp only [imb, m, a', b']
    exact_mod_cast hb
  have hexp := expect_le_expect (fun s (_ : s ∈ (univ : Finset (Bits V₀))) => hpr s)
  rw [← mul_expect, expect_add_distrib, Fintype.expect_const, ← mul_expect, expect_card_halfSet,
    Fintype.card_coe] at hexp
  have hfinal := hmatch.trans hexp
  change _ ≤ (∑ t : T, m t)/(T.card:ℝ) + (V₀.card:ℝ)*R/(2*(T.card:ℝ))
  have hd2 : 48*Real.sqrt (2*(gmax:ℝ)) = 2*D := by dsimp [D]; ring
  rw [hd2, show (∑ t : T, m t)/(T.card:ℝ) + (V₀.card:ℝ)*R/(2*(T.card:ℝ)) =
    ((∑ t : T, m t)+(R:ℝ)*((V₀.card:ℝ)/2))/(T.card:ℝ) by ring]
  apply (le_div_iff₀ hQ).mpr
  rw [div_mul_eq_mul_div, show (2:ℝ)*D = D*2 by ring, ← div_div]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  simpa only [mul_comm (2:ℝ)] using hfinal

end
end Reconstruction.LayoutMoments
