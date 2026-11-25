import LayoutMoments
import LayoutMomentsSelection
import LayoutMismatch

namespace Reconstruction.LayoutMoments

open Finset LayoutBudget Polynomial Matrix
open scoped BigOperators Classical Polynomial
noncomputable section

private theorem walk_eq_weight {ι : Type*} [Fintype ι] (b : Bits ι) :
    walk b = (Fintype.card ι : ℝ)-2*LayoutMismatch.weight b := by
  have he (i : ι) : sign (b i) = 1-2*(if b i = true then (1:ℝ) else 0) := by
    cases b i <;> norm_num [sign]
  simp only [walk, he, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_one,
    LayoutMismatch.weight, LayoutMismatch.ones, sum_boole]

private theorem sum_walk_by_weight {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℕ → ℝ) :
    (∑ b : Bits ι, f (LayoutMismatch.weight b)) =
      ∑ i ∈ range (Fintype.card ι+1), (Fintype.card ι).choose i*f i := by
  classical
  let e : Bits ι ≃ Finset ι := {
    toFun := LayoutMismatch.ones
    invFun := fun s i => decide (i ∈ s)
    left_inv := fun b => by
      funext i
      cases h : b i <;> simp [LayoutMismatch.ones, h]
    right_inv := fun b => by ext i; simp [LayoutMismatch.ones] }
  have he (b : Bits ι) : f (LayoutMismatch.weight b) = f (e b).card := rfl
  simp only [he]
  rw [e.sum_comp (fun b : Finset ι => f b.card)]
  have hu : (univ : Finset ι).powerset = univ := by ext b; simp
  simpa only [hu, card_univ, nsmul_eq_mul] using
    (sum_powerset_apply_card f (x := (univ : Finset ι)))

private theorem cast_truncated (h R i : ℕ) :
    ((h-R-2*i : ℕ) : ℝ) = max 0 ((h:ℝ)-R-2*i) := by
  rw [Nat.sub_sub]
  by_cases hx : R+2*i ≤ h
  · have he : (R:ℝ)+2*i ≤ h := by exact_mod_cast hx
    rw [Nat.cast_sub hx, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      max_eq_right (by linarith only [he])]
    ring
  · rw [Nat.sub_eq_zero_of_le (by omega : h ≤ R+2*i), Nat.cast_zero, max_eq_left]
    have he : (h:ℝ) ≤ R+2*i := by exact_mod_cast (show h ≤ R+2*i by omega)
    linarith

/-- The exact binomial normalization of Theorem 4 is the expected walk excess. -/
theorem cast_phi_eq_expect (R h : ℕ) :
    (LayoutMismatch.phi R h : ℝ) = 𝔼 b : Bits (Fin h), max 0 (walk b-R) := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  simp_rw [walk_eq_weight, Fintype.card_fin,
    show ∀ i : ℕ, (h:ℝ)-2*i-R = (h:ℝ)-R-2*i by intro; ring, ← cast_truncated]
  rw [sum_walk_by_weight (ι := Fin h) (fun i => ((h-R-2*i : ℕ):ℝ)), Fintype.card_fin]
  simp only [LayoutMismatch.phi, LayoutMismatch.chooseExcess, Rat.cast_div, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_mul]

/-- In the degree-zero, one-node case of equation (7), a foreign incidence
contributes one unit of rank, and a matched incidence contributes zero. -/
theorem two_mul_phi_zero_of_le_one {h : ℕ} (hh : h ≤ 1) :
    2 * LayoutMismatch.phi 0 h = (h:ℚ) := by
  interval_cases h <;>
    norm_num [LayoutMismatch.phi, LayoutMismatch.chooseExcess, Finset.sum_range_succ]

def windowConstant (β : ℝ) : ℝ := 16/β

def rankConstant (β : ℝ) : ℝ := β/(24*(windowConstant β+1))

def nodeWindow (β : ℝ) (R : ℕ) : ℕ := ⌈windowConstant β*((R:ℝ)+1)^2⌉₊

private theorem nodeWindow_bounds {β : ℝ} (hβ : 0 < β) (R : ℕ) :
    (16:ℝ)*((R:ℝ)+1)^2 ≤ β*(nodeWindow β R : ℝ) ∧
    (nodeWindow β R : ℝ) ≤ (windowConstant β+1)*((R:ℝ)+1)^2 ∧ 0 < nodeWindow β R := by
  let x := windowConstant β*((R:ℝ)+1)^2
  have hxp : 0 < x := by dsimp [x, windowConstant]; positivity
  have hxlo : x ≤ nodeWindow β R := Nat.le_ceil x
  have hxhi : (nodeWindow β R : ℝ) < x+1 := Nat.ceil_lt_add_one hxp.le
  have hR : 1 ≤ ((R:ℝ)+1)^2 := by nlinarith only [Nat.cast_nonneg (α := ℝ) R, sq_nonneg (R:ℝ)]
  refine ⟨?_, ?_, by exact_mod_cast (hxp.trans_le hxlo)⟩
  · calc
      _ = β*x := by dsimp [x, windowConstant]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hxlo hβ.le
  · change _ ≤ (windowConstant β+1)*((R:ℝ)+1)^2
    dsimp only [x] at hxhi
    linarith only [hxhi, hR]

/-- Finite arithmetic transfer of the exact binomial rank bound from Theorem 4. -/
theorem node_average_ge {V : Type*} [Fintype V] (h : V → ℕ) (R : ℕ) {β m : ℝ}
    (hβ : 0 < β) (hmax : ∀ v, h v ≤ nodeWindow β R)
    (hmean : β*(Fintype.card V:ℝ)*nodeWindow β R ≤ ∑ v, (h v:ℝ))
    (hm : 2*(∑ v, (LayoutMismatch.phi R (h v):ℝ)) ≤ m) :
    rankConstant β*(Fintype.card V:ℝ)/((R:ℝ)+1) ≤ m/(nodeWindow β R : ℝ) := by
  classical
  let k := nodeWindow β R
  obtain ⟨hklo, hkhi, hkpos⟩ := nodeWindow_bounds hβ R
  let A : Finset V := univ.filter (fun v => β*(k:ℝ)/2 ≤ h v)
  have hA : β*(Fintype.card V:ℝ)/2 ≤ (A.card:ℝ) :=
    heavy_mismatch_count h k hkpos β hβ.le hmax hmean
  have hφ (v : V) : 0 ≤ (LayoutMismatch.phi R (h v):ℝ) := by
    rw [cast_phi_eq_expect]
    exact expect_nonneg (fun _ _ => le_max_left _ _)
  have hpt (v : V) (hv : v ∈ A) : ((R:ℝ)+1)/24 ≤ (LayoutMismatch.phi R (h v):ℝ) := by
    have hv' := (mem_filter.mp hv).2
    have hheavy : (8:ℝ)*((R:ℝ)+1)^2 ≤ h v := by
      change β*(nodeWindow β R : ℝ)/2 ≤ (h v:ℝ) at hv'
      linarith only [hklo, hv']
    have hs : 2*((R:ℝ)+1) ≤ Real.sqrt ((h v:ℝ)/2) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      nlinarith only [hheavy]
    rw [cast_phi_eq_expect]
    have he := expect_walk_excess (ι := Fin (h v)) R (by simpa using hheavy)
    rw [Fintype.card_fin] at he
    linarith only [he, hs]
  have h25 : β*(Fintype.card V:ℝ)*((R:ℝ)+1)/24 ≤ m := by
    have hsum := sum_le_sum (fun v hv => hpt v hv)
    rw [sum_const, nsmul_eq_mul] at hsum
    have hinc := sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun v _ _ => hφ v)
    have hmul := mul_le_mul_of_nonneg_right hA (show 0 ≤ ((R:ℝ)+1)/24 by positivity)
    linarith only [hm, hsum, hinc, hmul]
  have hK : 0 < (k:ℝ) := by exact_mod_cast hkpos
  have hC : 0 < windowConstant β+1 := by unfold windowConstant; positivity
  have hRp : 0 < (R:ℝ)+1 := by positivity
  have hconst : 0 ≤ rankConstant β*(Fintype.card V:ℝ)/((R:ℝ)+1) := by
    unfold rankConstant
    positivity
  apply (le_div_iff₀ hK).mpr
  calc
    _ ≤ (rankConstant β*(Fintype.card V:ℝ)/((R:ℝ)+1)) *
        ((windowConstant β+1)*((R:ℝ)+1)^2) := mul_le_mul_of_nonneg_left hkhi hconst
    _ = β*(Fintype.card V:ℝ)*((R:ℝ)+1)/24 := by
      unfold rankConstant
      field_simp
    _ ≤ _ := h25

/-- Corollary 5, equation (10), and the Q-k+1 individual conclusion. The exact
mismatch-rank inequality is obtained from the physical tensor theorem. -/
theorem corollary_five {V I G Factor : Type*} [DecidableEq V] [DecidableEq I]
    [Fintype G] [DecidableEq G] {M : I → G → Type*} [∀ t g, Fintype (M t g)]
    (V₀ : Finset V) (nodes : Finset I) (node : I → ℚ) (R : ℕ)
    (a : I → V → G) (b : I → Factor → G) (scope : Factor → V → Prop)
    (P : Factor → V → V → ℚ[X])
    (C : ∀ t g, Matrix (M t g) (GroupFiber (a t) g) ℚ)
    (menu : V₀ → Finset Factor) (δ : ℝ) (Δ : ℕ)
    (hV : V₀.Nonempty) (hδ : 0 < δ)
    (hne : ∀ v, (menu v).Nonempty) (hsize : ∀ v, (menu v).card ≤ Δ)
    (hscope : ∀ v f, f ∈ menu v → scope f v.val)
    (hdemand : ∀ t ∈ nodes, δ*(V₀.card:ℝ) ≤
      ∑ v : V₀, ∑ f ∈ menu v, if a t v.val ≠ b t f then (1:ℝ) else 0)
    (hnodes : Set.InjOn node (↑nodes : Set I)) (hnonzero : ∀ t ∈ nodes, node t ≠ 0)
    (hzero : ∀ f v, scope f v → ∀ w, (P f v w).eval 0 = if v = w then 1 else 0)
    (hdegree : ∀ f v, scope f v → ∀ w, (P f v w).natDegree ≤ R)
    (hforeign : ∀ t ∈ nodes, ∀ f v, scope f v → ∀ g, b t f ≠ g →
      (fun w : GroupFiber (a t) g => (P f v w.val).eval (node t)) ∈
        Submodule.span ℚ (Set.range (C t g).row))
    (hwindow : nodeWindow (δ/(Δ:ℝ)) R ≤ nodes.card) :
    let β := δ/(Δ:ℝ)
    let k := nodeWindow β R
    let B := rankConstant β*(V₀.card:ℝ)/((R:ℝ)+1)
    let m (t : I) : ℝ := measurementRank (fun v : V₀ => v.val) (a t) (C t)
    0 < windowConstant β ∧ 0 < rankConstant β ∧
      (∀ T ⊆ nodes, T.card = k → B ≤ (∑ t ∈ T, m t)/(k:ℝ)) ∧
      nodes.card-k+1 ≤ (nodes.filter fun t => B ≤ m t).card := by
  classical
  dsimp only
  let β := δ/(Δ:ℝ)
  let k := nodeWindow β R
  let B := rankConstant β*(V₀.card:ℝ)/((R:ℝ)+1)
  let m (t : I) : ℝ := measurementRank (fun v : V₀ => v.val) (a t) (C t)
  change 0 < windowConstant β ∧ 0 < rankConstant β ∧
    (∀ T ⊆ nodes, T.card = k → B ≤ (∑ t ∈ T, m t)/(k:ℝ)) ∧
    nodes.card-k+1 ≤ (nodes.filter fun t => B ≤ m t).card
  have hΔ : 0 < Δ := by
    obtain ⟨v,hv⟩ := hV
    exact (card_pos.mpr (hne ⟨v,hv⟩)).trans_le (hsize ⟨v,hv⟩)
  have hΔ' : 0 < (Δ:ℝ) := by exact_mod_cast hΔ
  have hβ : 0 < β := div_pos hδ hΔ'
  obtain ⟨hklo, _, hkpos⟩ := nodeWindow_bounds hβ R
  have havg (T : Finset I) (hT : T ⊆ nodes) (hTk : T.card = k) :
      B ≤ (∑ t ∈ T, m t)/(k:ℝ) := by
    let a' (t : I) (v : V₀) := a t v.val
    obtain ⟨chosen, hchosen, _, hselect⟩ := exists_factor_selection T a' b menu δ Δ hΔ hne hsize
      (fun t ht => by simpa only [Fintype.card_coe] using hdemand t (hT ht))
    let h (v : V₀) := mismatchCount T a' b v (chosen v)
    have hmax (v : V₀) : h v ≤ k := by
      rw [← hTk]
      exact card_le_card (filter_subset _ _)
    have hsum : (∑ v : V₀, (h v:ℝ)) ≤ (V₀.card:ℝ)*k := by
      simpa only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] using
        (sum_le_sum (fun v (_ : v ∈ (univ : Finset V₀)) =>
          (by exact_mod_cast hmax v : (h v:ℝ) ≤ k)))
    rw [Fintype.card_coe, hTk] at hselect
    change β*(V₀.card:ℝ)*k ≤ ∑ v : V₀, (h v:ℝ) at hselect
    have hk0 : 0 < (k:ℝ) := by exact_mod_cast hkpos
    have hV0 : 0 < (V₀.card:ℝ) := by exact_mod_cast card_pos.mpr hV
    have hβ1 : β ≤ 1 := by
      apply le_of_mul_le_mul_right _ (mul_pos hV0 hk0)
      nlinarith only [hselect.trans hsum]
    have hRk : R < k := by
      have hklo' : (16:ℝ)*((R:ℝ)+1)^2 ≤ k :=
        hklo.trans (mul_le_of_le_one_left hk0.le hβ1)
      exact_mod_cast (show (R:ℝ)<k by
        nlinarith only [hklo', Nat.cast_nonneg (α := ℝ) R, sq_nonneg (R:ℝ)])
    have hm := LayoutMismatch.mismatch_rank V₀ T node R a b scope chosen
      (fun v => hscope v (chosen v) (hchosen v)) P C
      (hnodes.mono hT) (fun t ht => hnonzero t (hT ht)) (by simpa only [hTk] using hRk) hzero hdegree
      (fun t ht => hforeign t (hT ht))
    have hm' : 2*(∑ v : V₀, (LayoutMismatch.phi R (h v):ℝ)) ≤ ∑ t ∈ T, m t := by
      rw [← T.sum_coe_sort]
      have he := (Rat.cast_le (K := ℝ)).mpr hm
      simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sum, Rat.cast_natCast, Nat.cast_sum,
        h, m, mismatchCount, a'] using he
    simpa only [Fintype.card_coe] using
      (node_average_ge h R hβ hmax (by simpa only [Fintype.card_coe] using hselect) hm')
  exact ⟨by unfold windowConstant; positivity, by unfold rankConstant windowConstant; positivity,
    havg, many_individual_nodes nodes m B k hkpos hwindow havg⟩

end
end Reconstruction.LayoutMoments
