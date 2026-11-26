import S6Cells
import S6Tune

namespace Section6

open Finset Filter
open scoped BigOperators

noncomputable section

abbrev SlotLayout (n copies Q r : ℕ) := Placement (Fin n) (Fin copies) (Fin Q) (Fin r)

/-- The visit functions account for the three enumerations on one routine call.
The summary and the largest group may be observed at different nodes. -/
structure RoutineVisits {n copies Q r : ℕ} (P : SlotLayout n copies Q r)
    (window : Finset ℕ) (q T : ℕ) where
  summaryNode : Fin Q
  groupNode : Fin Q
  group : Fin r
  largest : ∀ g : Fin r,
    (univ.filter (fun v => P.first v groupNode = g)).card ≤
      (univ.filter (fun v => P.first v groupNode = group)).card
  visited : Visits (Fin n) q (Set.range (actualSummary P window summaryNode))
    ({v : Fin n // P.first v groupNode = group} → Bool) T

theorem cap_implies_volume {n copies Q r : ℕ} (P : SlotLayout n copies Q r)
    (hn : 0 < n)
    (hcap : ∀ u, (loadCell P u : ℝ) * cubeSize (Fin Q) (Fin r) ≤ 2 * (occupied P).card) :
    (r : ℝ) ^ (2*Q) ≤ 2 * (occupied P).card := by
  obtain ⟨x, hx⟩ := P.occurs ⟨0, hn⟩
  have hp : 0 < loadCell P x.2 :=
    card_pos.mpr ⟨x, by simp [occupied, hx]⟩
  have h := hcap x.2
  have hp' : (1 : ℝ) ≤ (loadCell P x.2 : ℝ) := by exact_mod_cast hp
  have hD : (r : ℝ) ^ (2*Q) = (cubeSize (Fin Q) (Fin r) : ℝ) := by simp [pow_mul, pow_two]
  rw [hD]
  simpa using (mul_le_mul_of_nonneg_right hp' (show (0 : ℝ) ≤ cubeSize (Fin Q) (Fin r) by positivity)).trans h

lemma log_budget_from_cap {n copies Q r : ℕ} (P : SlotLayout n copies Q r)
    (hn : 0 < n) (hr : 2 ≤ r)
    (hcap : ∀ u, (loadCell P u : ℝ) * cubeSize (Fin Q) (Fin r) ≤ 2 * (occupied P).card)
    (hM : Real.log (2 * ((occupied P).card : ℝ)) ≤ 2 * L n) :
    (Q : ℝ) * Real.log r ≤ L n := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hl := Real.log_le_log (pow_pos hrp _) (cap_implies_volume P hn hcap)
  rw [Real.log_pow] at hl
  push_cast at hl
  linarith

lemma rank_le_lg {n copies Q r q T : ℕ} {P : SlotLayout n copies Q r} {window : Finset ℕ}
    (scan : RoutineVisits P window q T) :
    ((actualMatrix P window).rank : ℝ) ≤ lg T := by
  classical
  letI : Fintype (Set.range (actualSummary P window scan.summaryNode)) := Fintype.ofFinite _
  apply le_lg_of_two_pow_le
  apply (FA1 P window scan.summaryNode).2.trans
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (visit_counts scan.visited).2.1

lemma group_le_lg {n copies Q r q T : ℕ} {P : SlotLayout n copies Q r} {window : Finset ℕ}
    (hr : 0 < r) (scan : RoutineVisits P window q T) : (n : ℝ) ≤ r * lg T := by
  classical
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨g, hg⟩ := largest_group_ge_average (fun v => P.first v scan.groupNode)
  have hn : n ≤ r * (univ.filter (fun v => P.first v scan.groupNode = scan.group)).card := by
    simpa only [Fintype.card_fin] using hg.trans (Nat.mul_le_mul_left _ (scan.largest g))
  have ht := (visit_counts scan.visited).2.2
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype] at ht
  have hh := le_lg_of_two_pow_le _ _ ht
  exact (show (n : ℝ) ≤ r * ((univ.filter (fun v => P.first v scan.groupNode = scan.group)).card : ℝ)
    by exact_mod_cast hn).trans (mul_le_mul_of_nonneg_left hh (by positivity))

/-- The finite all-layout lower bound with size-only conditions exposed. -/
theorem FA4_at_size {n copies Q r R q T : ℕ} (P : SlotLayout n copies Q r)
    (window : Finset ℕ) (scan : RoutineVisits P window q T) (κ K : ℝ)
    (hκ : 0 < κ) (hK : 0 < K) (hn : 0 < n) (hr : 2 ≤ r) (hR : 0 < R) (hQR : R < Q)
    (hw : window.card = R) (hL : 0 < L n) (hl : 1 ≤ l n) (hKQ : 256 ≤ K * l n)
    (hsize : 1 ≤ (n : ℝ) * alpha n)
    (hs₁ : alpha n ≤ 1) (hs₂ : 2 * K * l n * alpha n ≤ κ) (hs₃ : 32 * alpha n ≤ κ)
    (hs₄ : alpha n ≤ Real.exp (-(l n / 4)))
    (hs₅ : alpha n ≤ (Real.exp (-16) / 16) * Real.exp (-(l n / 8)))
    (hs₆ : 2 ≤ (min κ 1 / 512) * n * beta n)
    (hq : ⌊κ * (n : ℝ) * R / Q⌋₊ ≤ q)
    (hcap : ∀ u, (loadCell P u : ℝ) * cubeSize (Fin Q) (Fin r) ≤ 2 * (occupied P).card)
    (hM : Real.log (2 * ((occupied P).card : ℝ)) ≤ 2 * L n)
    (hdensity : K * l n < Q → 2 * (occupied P).card * xi ^ Q ≤ (n : ℝ) / 2) :
    (min κ 1 / 4096) * (n : ℝ) * alpha n ≤ lg T := by
  classical
  apply optimize_visits n r Q R q T κ K hκ hK hn hr hR hQR hL hl hKQ
    (log_budget_from_cap P hn hr hcap hM) hsize hs₁ hs₂ hs₃ hs₄ hs₅ hs₆
  · have hh := (Nat.floor_lt (by positivity)).mp (Nat.lt_succ_of_le hq)
    simpa only [Nat.cast_succ] using hh
  · exact group_le_lg (by omega) scan
  · have ht := (visit_counts scan.visited).1
    simpa using (taylor_ge_two_pow (V := Fin n) q).trans ht
  · intro j hj
    have ht := (visit_counts scan.visited).1
    simpa using (taylor_ge_choose (V := Fin n) q j hj).trans ht
  · intro hlarge hsmall
    have hQ : 256 ≤ Q := by
      exact_mod_cast (show (256 : ℝ) ≤ Q from hKQ.trans hlarge.le)
    have hdiag := FA3 P window R (by simpa using hr) (by simpa using hQ) hw
      (by simpa using hsmall) hcap (by simpa using hdensity hlarge)
    exact (show (Real.exp (-16) / 16) * n * Real.exp (-(64 * (R : ℝ)^2 / Q)) ≤
      (actualMatrix P window).rank by simpa using hdiag).trans (rank_le_lg scan)

lemma direct_nominal_order (n R Q : ℕ) :
    ⌊(1 : ℝ) * (n : ℝ) * R / Q⌋₊ ≤ 3 * n * R / Q := by
  by_cases hQ : Q = 0
  · simp [hQ]
  have hQ0 : 0 < (Q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hQ
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt (by positivity)).mpr
  apply (div_lt_iff₀ hQ0).mpr
  have h := Nat.lt_mul_div_succ (3*n*R) (Nat.pos_of_ne_zero hQ)
  have hr : (3 : ℝ) * n * R < ((3*n*R/Q : ℕ) + 1 : ℝ) * Q := by exact_mod_cast (by simpa [Nat.mul_comm Q] using h : 3*n*R < (3*n*R/Q+1)*Q)
  push_cast
  nlinarith only [hr, show 0 ≤ (n : ℝ) * R by positivity]

lemma supplied_nominal_order (n k tests precision R Q : ℕ) (hk : 0 < k) (hp : n ≤ precision - 1) :
    n * R / Q ≤ k * (tests + 2 * (precision - 1)) * R / Q := by
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_right
  calc
    n ≤ tests + 2 * (precision - 1) := by omega
    _ ≤ _ := Nat.le_mul_of_pos_left _ hk

#print axioms cap_implies_volume
#print axioms rank_le_lg
#print axioms group_le_lg
#print axioms FA4_at_size
#print axioms direct_nominal_order
#print axioms supplied_nominal_order

end
end Section6




