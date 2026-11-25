import VisitRuntimeNumerical
import LayoutMomentsPrincipal
import LayoutMomentsMismatch

open scoped BigOperators

namespace Reconstruction.VisitRuntime

open LayoutBudget (GroupFiber)

noncomputable section

variable {V F : Type*} [Fintype V] [DecidableEq V] {Q r R : ℕ}

/-- The actual candidate incidences, with the per-node mismatch demand. -/
structure CandidateFactors (L : PhysicalLayout V F Q r R) (U : Finset V) (δ : ℝ) (Δ : ℕ) where
  menu : U → Finset F
  nonempty : ∀ u, (menu u).Nonempty
  size : ∀ u, (menu u).card ≤ Δ
  incident : ∀ u f, f ∈ menu u → L.scope f u.val
  mismatch : ∀ t, δ*(U.card:ℝ) ≤
    ∑ u : U, ∑ f ∈ menu u, if L.source t u.val ≠ L.target t f then (1:ℝ) else 0

omit [Fintype V] in
theorem CandidateFactors.corollaryTwo {L : PhysicalLayout V F Q r R} {U : Finset V} {δ G : ℝ} {Δ : ℕ}
    (C : CandidateFactors L U δ Δ) (hU : U.Nonempty) (hQ : 0 < Q) (hδ : 0 < δ) (hG : 0 ≤ G)
    (hg : ∀ t g, (Fintype.card (GroupFiber (fun u : U => L.source t u.val) g):ℝ) ≤ G) :
    CorollaryTwoEstimate (L.rankOn U) U.card R (δ/(Δ:ℝ)) G := by
  classical
  let G₀ := ⌊G⌋₊
  have hh := LayoutMoments.corollary_two U (Finset.univ : Finset (Fin Q)) L.node R
    L.source L.target L.scope L.poly L.measure C.menu δ Δ G₀ hU
    (Finset.card_pos.mp (by simpa using hQ)) C.nonempty C.size C.incident
    (fun t _ => C.mismatch t) (fun t _ g => Nat.le_floor (hg t g)) L.nodes_injective.injOn
    L.constant L.degree (fun t _ => L.foreign t)
  have hb := hh
  change _ ≤ (∑ t : (Finset.univ : Finset (Fin Q)), (L.rankOn U t.val:ℝ))/Finset.univ.card +
    (U.card:ℝ)*R/(2*((Finset.univ : Finset (Fin Q)).card:ℝ)) at hb
  rw [(Finset.univ : Finset (Fin Q)).sum_coe_sort (fun t => (L.rankOn U t:ℝ)),
    Finset.card_univ, Fintype.card_fin] at hb
  refine le_trans ?_ hb
  have hG₀ : 0 < G₀ := by
    obtain ⟨u,hu⟩ := hU
    let t : Fin Q := ⟨0,hQ⟩
    haveI : Nonempty (GroupFiber (fun u : U => L.source t u.val) (L.source t u)) := ⟨⟨⟨u,hu⟩, rfl⟩⟩
    exact Fintype.card_pos.trans_le (Nat.le_floor (hg t (L.source t u)))
  have hG₀' : 0 < (G₀:ℝ) := by exact_mod_cast hG₀
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [Nat.floor_le hG])) (by norm_num)

omit [Fintype V] in
theorem CandidateFactors.corollaryFive {L : PhysicalLayout V F Q r R} {U : Finset V} {δ : ℝ} {Δ : ℕ}
    (C : CandidateFactors L U δ Δ) (hU : U.Nonempty) (hδ : 0 < δ) :
    CorollaryFiveEstimate (L.rankOn U) U.card R
      (LayoutMoments.rankConstant (δ/(Δ:ℝ))) (LayoutMoments.windowConstant (δ/(Δ:ℝ))) := by
  intro S hS
  have hwin : LayoutMoments.nodeWindow (δ/(Δ:ℝ)) R ≤ (Finset.univ : Finset (Fin Q)).card := by
    rw [LayoutMoments.nodeWindow, ← hS]
    exact Finset.card_le_card (Finset.subset_univ S)
  have h := (LayoutMoments.corollary_five U (Finset.univ : Finset (Fin Q)) L.node R
    L.source L.target L.scope L.poly L.measure C.menu δ Δ hU hδ
    C.nonempty C.size C.incident (fun t _ => C.mismatch t) L.nodes_injective.injOn
    (fun t _ => L.nodes_ne_zero t) L.constant L.degree (fun t _ => L.foreign t) hwin).2.2.1
      S (Finset.subset_univ S) hS
  simpa only [LayoutMoments.nodeWindow, ← hS, PhysicalLayout.rankOn] using h

omit [Fintype V] in
/-- The single-node instance of (7) is the coordinate-rank bound for degree-zero rows. -/
theorem CandidateFactors.zeroDegree {L : PhysicalLayout V F Q r 0} {U : Finset V} {δ : ℝ} {Δ : ℕ}
    (C : CandidateFactors L U δ Δ) (hU : U.Nonempty) (t : Fin Q) :
    (δ/(Δ:ℝ))*(U.card:ℝ) ≤ L.rankOn U t := by
  classical
  have hΔ : 0 < Δ := by
    obtain ⟨u,hu⟩ := hU
    exact (Finset.card_pos.mpr (C.nonempty ⟨u,hu⟩)).trans_le (C.size ⟨u,hu⟩)
  obtain ⟨chosen, hchosen, _, hselect⟩ := LayoutMoments.exists_factor_selection {t}
    (fun i (v : U) => L.source i v.val) L.target C.menu δ Δ hΔ C.nonempty C.size
    (fun i _ => by simpa only [Fintype.card_coe] using C.mismatch i)
  have hrank := LayoutMismatch.mismatch_rank U {t} L.node 0 L.source L.target L.scope chosen
    (fun u => C.incident u _ (hchosen u)) L.poly L.measure L.nodes_injective.injOn
    (fun i _ => L.nodes_ne_zero i) (by simp) L.constant L.degree (fun i _ => L.foreign i)
  have hphi (u : U) : 2 * LayoutMismatch.phi 0
      (({t} : Finset (Fin Q)).filter fun i => L.source i u.val ≠ L.target i (chosen u)).card =
      (LayoutMoments.mismatchCount {t} (fun i (v : U) => L.source i v.val) L.target u (chosen u):ℚ) := by
    unfold LayoutMoments.mismatchCount
    by_cases hm : L.source t u.val = L.target t (chosen u)
    · have he : (({t} : Finset (Fin Q)).filter fun i => L.source i u.val ≠ L.target i (chosen u)) = ∅ := by
        ext i
        simp (config := {contextual := true}) [hm]
      rw [he]
      norm_num [LayoutMismatch.phi, LayoutMismatch.chooseExcess]
    · have he : (({t} : Finset (Fin Q)).filter fun i => L.source i u.val ≠ L.target i (chosen u)) = {t} := by
        ext i
        simp (config := {contextual := true}) [hm]
      rw [he]
      norm_num [LayoutMismatch.phi, LayoutMismatch.chooseExcess, Finset.sum_range_succ]
  rw [Finset.mul_sum] at hrank
  simp_rw [hphi] at hrank
  change _ ≤ ((∑ i : ({t} : Finset (Fin Q)), L.rankOn U i.val : ℕ):ℚ) at hrank
  rw [({t} : Finset (Fin Q)).sum_coe_sort (L.rankOn U), Finset.sum_singleton] at hrank
  simp only [Fintype.card_coe, Finset.card_singleton, Nat.cast_one, mul_one] at hselect
  exact hselect.trans (by exact_mod_cast hrank)

end

end Reconstruction.VisitRuntime
