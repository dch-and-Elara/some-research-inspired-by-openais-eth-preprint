import VisitRuntimeRank

open Filter
open scoped BigOperators Topology

namespace Reconstruction.VisitRuntime

open LayoutBudget (GroupFiber)

noncomputable section

theorem selected_group_le {V F : Type*} [Fintype V] [DecidableEq V] {Q r R : ℕ}
    (L : PhysicalLayout V F Q r R) (U : Finset V) (t : Fin Q) (g : Fin r) :
    Fintype.card (GroupFiber (fun u : U => L.source t u.val) g) ≤ L.groupSize t g :=
  Fintype.card_le_of_embedding
    (⟨fun u => (⟨u.val.val,u.property⟩ : GroupFiber (L.source t) g),
      fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun u : GroupFiber (L.source t) g => u.val) h))⟩)

theorem arbitraryNodeScale_sublinear (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K*arbitraryNodeScale N ≤ (N:ℝ) := by
  have h := (tendsto_rpow_atTop (show (0:ℝ) < 1/3 by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_gt_atTop (0:ℕ), h.eventually_ge_atTop K] with N hN hk
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  calc
    _ ≤ ((N:ℝ)^(1/3:ℝ))*arbitraryNodeScale N :=
      mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hN'.le _)
    _ = _ := by unfold arbitraryNodeScale; rw [← Real.rpow_add hN']; norm_num

/-- Runtime logarithm from the raw candidate lists and balanced physical groups.
This form also allows the ranked variables to be a fixed positive fraction of
the variables of the call, as in Appendix A. -/
theorem balanced_from_candidates {δ ρ c₀ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hρ : 0 < ρ) (hc₀ : 0 < c₀) (r₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ {V F : Type*} [Fintype V] [DecidableEq V]
      {Q r R d₀ T : ℕ} {L : PhysicalLayout V F Q r R} (_W : Visits L d₀ T) (U : Finset V),
      N₀ ≤ Fintype.card V → ρ*(Fintype.card V:ℝ) ≤ U.card → c₀*(Fintype.card V:ℝ) ≤ d₀ →
      L.balanced → (r₀ ≤ r → Nonempty (CandidateFactors L U δ Δ)) →
      C*arbitraryNodeScale (Fintype.card V) ≤ Real.log T := by
  have hβ : 0 < δ/(Δ:ℝ) := div_pos hδ (by exact_mod_cast hΔ)
  obtain ⟨C,hC,hmain⟩ := theorem3_numerical hβ hc₀ hρ
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (hmain.and ((arbitraryNodeScale_sublinear r₀).and (eventually_ge_atTop 1)))
  refine ⟨C,hC,N₀,?_⟩
  intro V F _ _ Q r R d₀ T L W U hN hn hd hb hc
  let N := Fintype.card V
  let p := arbitraryNodeScale N
  obtain ⟨ht,hsub,hN1⟩ := hN₀ N hN
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 ≤ p := Real.rpow_nonneg hN0.le _
  have hr : 0 < (r:ℝ) := by exact_mod_cast W.groups_pos
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hU : U.Nonempty := Finset.card_pos.mp (by exact_mod_cast (mul_pos hρ hN0 |>.trans_le hn))
  let B := W.bounds U
  apply ht U.card Q r R d₀ T (L.rankOn U) B hn hd
  let G := 2*(N:ℝ)/(r:ℝ)
  have hG : 0 < G := div_pos (by positivity) hr
  by_cases hGbig : p ≤ G
  · left
    refine (mul_le_mul_of_nonneg_right (show p/2 ≤ (N:ℝ)/(r:ℝ) by
      dsimp [G] at hGbig
      rw [mul_div_assoc] at hGbig
      linarith) hlog).trans
      B.log_largest
  · have hrmin : r₀ ≤ r := by
      by_contra! hrlt
      have hr' : (r:ℝ) ≤ r₀ := by exact_mod_cast hrlt.le
      have hg := (mul_le_mul_of_nonneg_right hr' hp).trans hsub
      apply hGbig
      apply (le_div_iff₀ hr).mpr
      nlinarith only [hg, hN0]
    obtain ⟨H⟩ := hc hrmin
    refine Or.inr ⟨G,hG,(lt_of_not_ge hGbig).le, H.corollaryTwo hU W.nodes_pos hδ hG.le ?_⟩
    intro t g
    exact (Nat.cast_le.mpr (selected_group_le L U t g)).trans (hb t g)

/-- The Section 6 unbalanced variant with a largest-group scan at every node. -/
theorem unbalanced_from_candidates {δ c₀ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ {V F : Type*} [Fintype V] [DecidableEq V]
      {Q r R d₀ T : ℕ} {L : PhysicalLayout V F Q r R} (_W : Visits L d₀ T),
      N₀ ≤ Fintype.card V → c₀*(Fintype.card V:ℝ) ≤ d₀ → ScansAtEveryNode L T →
      ((∀ t g, 2*L.groupSize t g ≤ Fintype.card V) →
        Nonempty (CandidateFactors L Finset.univ δ Δ)) →
      C*arbitraryNodeScale (Fintype.card V) ≤ Real.log T := by
  have hβ : 0 < δ/(Δ:ℝ) := div_pos hδ (by exact_mod_cast hΔ)
  obtain ⟨C,hC,hmain⟩ := theorem3_numerical hβ hc₀ (show (0:ℝ) < 1 by norm_num)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (hmain.and ((arbitraryNodeScale_sublinear 2).and (eventually_ge_atTop 1)))
  refine ⟨C,hC,N₀,?_⟩
  intro V F _ _ Q r R d₀ T L W hN hd hscan hc
  let N := Fintype.card V
  let p := arbitraryNodeScale N
  obtain ⟨ht,hsub,hN1⟩ := hN₀ N hN
  have hp : 0 < p := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hU : (Finset.univ : Finset V).Nonempty := Finset.card_pos.mp (by simp; omega)
  apply ht (Finset.univ : Finset V).card Q r R d₀ T (L.rankOn Finset.univ) (W.bounds Finset.univ)
    (by simp [N]) hd
  by_cases hbig : ∃ t g, p ≤ (L.groupSize t g:ℝ)
  · obtain ⟨t,g,hg⟩ := hbig
    left
    exact (mul_le_mul_of_nonneg_right (show p/2 ≤ (L.groupSize t g:ℝ) by linarith)
      (Real.log_nonneg (by norm_num))).trans (log_of_pow_le (Visits.scan_pow_le_at_every_node hscan t g))
  · have hg (t : Fin Q) (g : Fin r) : (L.groupSize t g:ℝ) ≤ p := by
      exact (lt_of_not_ge (fun hu => hbig ⟨t,g,hu⟩)).le
    have hh (t : Fin Q) (g : Fin r) : 2 * L.groupSize t g ≤ Fintype.card V := by
      exact_mod_cast (show 2*(L.groupSize t g:ℝ) ≤ (N:ℝ) by linarith only [hg t g,hsub])
    obtain ⟨H⟩ := hc hh
    refine Or.inr ⟨p,hp,le_rfl,H.corollaryTwo hU W.nodes_pos hδ hp.le ?_⟩
    intro t g
    exact (Nat.cast_le.mpr (selected_group_le L Finset.univ t g)).trans (hg t g)

/-- The polynomial-schedule runtime from raw candidate lists, including the
constant-row case. -/
theorem scheduled_from_candidates {A δ ρ c₀ : ℝ} {Δ : ℕ} (hA : 0 < A) (hδ : 0 < δ)
    (hΔ : 0 < Δ) (hρ : 0 < ρ) (hc₀ : 0 < c₀) (r₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ {V F : Type*} [Fintype V] [DecidableEq V]
      {Q r R d₀ T : ℕ} {L : PhysicalLayout V F Q r R} (_W : Visits L d₀ T) (U : Finset V),
      N₀ ≤ Fintype.card V → ρ*(Fintype.card V:ℝ) ≤ U.card → c₀*(Fintype.card V:ℝ) ≤ d₀ →
      (r:ℝ)^(2*Q) ≤ (Fintype.card V:ℝ)^A →
      (r₀ ≤ r → Nonempty (CandidateFactors L U δ Δ)) →
      C*((Fintype.card V:ℝ)*scheduledRate (Fintype.card V)) ≤ Real.log T := by
  have hβ : 0 < δ/(Δ:ℝ) := div_pos hδ (by exact_mod_cast hΔ)
  have hκ : 0 < LayoutMoments.windowConstant (δ/(Δ:ℝ)) := by unfold LayoutMoments.windowConstant; positivity
  have hcβ : 0 < LayoutMoments.rankConstant (δ/(Δ:ℝ)) := by unfold LayoutMoments.rankConstant; positivity
  obtain ⟨C,hC,hmain⟩ := theorem6_numerical hA hc₀ hρ hβ hcβ hκ r₀
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hmain.and (eventually_ge_atTop 1))
  refine ⟨C,hC,N₀,?_⟩
  intro V F _ _ Q r R d₀ T L W U hN hn hd hsize hc
  obtain ⟨ht,hN1⟩ := hN₀ (Fintype.card V) hN
  have hN0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hU : U.Nonempty := Finset.card_pos.mp (by exact_mod_cast (mul_pos hρ hN0 |>.trans_le hn))
  refine ht U.card Q r R d₀ T (L.rankOn U) (W.bounds U) hn hd hsize ?_ ?_
  · intro hr
    obtain ⟨H⟩ := hc hr
    exact H.corollaryFive hU hδ
  · intro hr hR t
    subst R
    obtain ⟨H⟩ := hc hr
    exact H.zeroDegree hU t

end

end Reconstruction.VisitRuntime
