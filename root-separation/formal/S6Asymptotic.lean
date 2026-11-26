import S6Bridge

namespace Section6

open Filter
open scoped Topology

noncomputable section

def cutoffSlope (B : ℝ) := 256 + (B + 1) / (-Real.log xi)
def densityOffset (B : ℝ) := 2 * Real.log 2 - B * Real.log (Real.log 2)

lemma xi_pos : 0 < xi := mul_pos rootTwo_pos (by norm_num)
lemma logXi_neg : Real.log xi < 0 := Real.log_neg xi_pos xi_lt_one

lemma tendsto_L : Tendsto L atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_l : Tendsto l atTop atTop := Real.tendsto_log_atTop.comp tendsto_L

lemma eventually_log_power (c : ℝ) (hc : 0 < c) (d : ℕ) (s : ℝ) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, l n ^ d ≤ c * (L n) ^ s := by
  have h := ((isLittleO_log_rpow_rpow_atTop (d : ℝ) hs).bound hc)
  filter_upwards [tendsto_L.eventually h, tendsto_L.eventually_ge_atTop 1,
    tendsto_l.eventually_ge_atTop 1] with n hb hL hl
  have hl0 : 0 ≤ l n := by linarith
  have hL0 : 0 ≤ L n := by linarith
  change ‖(l n) ^ (d : ℝ)‖ ≤ c * ‖(L n) ^ s‖ at hb
  simpa only [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hl0 _),
    Real.norm_of_nonneg (Real.rpow_nonneg hL0 _)] using hb

lemma eventually_alpha_times_l (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, l n * alpha n ≤ c := by
  filter_upwards [eventually_log_power c hc 3 (1/2) (by norm_num),
    tendsto_L.eventually_gt_atTop 0] with n h hL
  rw [← Real.sqrt_eq_rpow] at h
  unfold alpha beta
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hL)).mpr (by nlinarith only [h])

lemma eventually_alpha_exp (c w : ℝ) (hc : 0 < c) (hw : w < 1/2) :
    ∀ᶠ n : ℕ in atTop, alpha n ≤ c * Real.exp (-(l n * w)) := by
  filter_upwards [eventually_log_power c hc 2 (1/2-w) (sub_pos.mpr hw),
    tendsto_L.eventually_gt_atTop 0] with n h hL
  have hpow : (L n) ^ (1/2-w : ℝ) = (L n) ^ (1/2 : ℝ) * (L n) ^ (-w) := by
    rw [← Real.rpow_add hL]
    congr 1
  have hexp : Real.exp (-(l n * w)) = (L n) ^ (-w) := by
    rw [Real.rpow_def_of_pos hL]
    unfold l
    ring_nf
  rw [hexp]
  unfold alpha beta
  rw [← mul_div_assoc, ← Real.sqrt_eq_rpow] at *
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hL)).mpr
  rw [hpow] at h
  nlinarith only [h]

lemma eventually_n_beta (b : ℝ) :
    ∀ᶠ n : ℕ in atTop, b ≤ (n : ℝ) * beta n := by
  have hs : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop := by
    rw [show (fun n : ℕ => √(n : ℝ)) = (fun n : ℕ => (n : ℝ) ^ (1/2 : ℝ)) from
      funext fun n => Real.sqrt_eq_rpow _]
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hs.eventually_ge_atTop b, tendsto_l.eventually_ge_atTop 1,
    tendsto_L.eventually_gt_atTop 0, eventually_ge_atTop (1 : ℕ)] with n hb hl hL hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : (n : ℝ) ≥ L n := by unfold L; linarith [Real.log_le_sub_one_of_pos hn0]
  apply hb.trans
  unfold beta
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hL)).mpr
  calc
    _ ≤ √(n : ℝ) * √(n : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _)
    _ = (n : ℝ) := by rw [← pow_two, Real.sq_sqrt hn0.le]
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hl hn0.le

lemma eventually_budget_offset (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, B * l n + densityOffset B ≤ L n := by
  let c := 1 / (2 * (B + 1))
  have hc : 0 < c := by unfold c; positivity
  filter_upwards [eventually_log_power c hc 1 1 one_pos,
    tendsto_L.eventually_ge_atTop (max 1 (2 * densityOffset B))] with n hp hL
  have hL1 : 1 ≤ L n := (le_max_left _ _).trans hL
  have hLo : 2 * densityOffset B ≤ L n := (le_max_right _ _).trans hL
  rw [pow_one, Real.rpow_one] at hp
  have hc' : B * c ≤ 1/2 := by
    unfold c
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have h₁ := mul_le_mul_of_nonneg_left hp hB
  have h₂ := mul_le_mul_of_nonneg_right hc' (show 0 ≤ L n by linarith)
  nlinarith only [h₁, h₂, hLo]

lemma log_M_le {n M : ℕ} (hM : 0 < M) (hL : 0 < L n) (B : ℝ)
    (hMupper : (M : ℝ) ≤ (n : ℝ) * (lg n) ^ B) :
    Real.log M ≤ L n + B * (l n - Real.log (Real.log 2)) := by
  have hn0 : (0 : ℝ) < n := by
    by_contra! hn
    have he : n = 0 := by exact_mod_cast (le_antisymm hn (Nat.cast_nonneg n))
    simp [L, he] at hL
  have h := Real.log_le_log (show (0 : ℝ) < M by exact_mod_cast hM) hMupper
  have hg : 0 < lg n := div_pos hL logTwo_pos
  rw [Real.log_mul hn0.ne' (Real.rpow_pos_of_pos hg _).ne', Real.log_rpow hg, lg,
    Real.log_div (show Real.log (n : ℝ) ≠ 0 from hL.ne') logTwo_pos.ne'] at h
  exact h

lemma density_from_large_Q {n M Q : ℕ} (hM : 0 < M) (hL : 0 < L n) (hl : 1 ≤ l n)
    (B : ℝ) (hB : 0 ≤ B) (hOffset : densityOffset B ≤ l n)
    (hMupper : (M : ℝ) ≤ n * (lg n) ^ B) (hlarge : cutoffSlope B * l n < Q) :
    2 * (M : ℝ) * xi ^ Q ≤ (n : ℝ) / 2 := by
  have hm := log_M_le hM hL B hMupper
  have hn : (0 : ℝ) < n := by
    have h : n ≠ 0 := by intro he; simp [L, he] at hL
    exact_mod_cast Nat.pos_of_ne_zero h
  have hK : cutoffSlope B * (-Real.log xi) ≥ B + 1 := by
    unfold cutoffSlope
    have hp : 0 < -Real.log xi := neg_pos.mpr logXi_neg
    calc
      _ = 256 * (-Real.log xi) + (B + 1) := by field_simp [logXi_neg.ne]; ring
      _ ≥ _ := by linarith only [mul_nonneg (by norm_num : (0 : ℝ) ≤ 256) hp.le]
  have hQl := mul_le_mul_of_nonneg_right hlarge.le (neg_pos.mpr logXi_neg).le
  have hKl := mul_le_mul_of_nonneg_right hK (show 0 ≤ l n by linarith)
  have hh : 2 * Real.log 2 + Real.log M + (Q : ℝ) * Real.log xi ≤ L n := by
    unfold densityOffset at hOffset
    linarith only [hm, hQl, hKl, hOffset]
  have hpos : (0 : ℝ) < M := by exact_mod_cast hM
  apply (Real.log_le_log_iff (show 0 < 2 * (M : ℝ) * xi ^ Q by exact mul_pos (by positivity) (pow_pos xi_pos _)) (show 0 < (n : ℝ) / 2 by positivity)).mp
  rw [Real.log_mul (by positivity) (pow_pos xi_pos _).ne', Real.log_mul (by norm_num)
    hpos.ne', Real.log_pow, Real.log_div hn.ne' (by norm_num)]
  unfold L at hh
  linarith only [hh]

/-- The paper's base-two rate. The optimizer used natural logarithms in n. -/
def paperRate (n : ℕ) := (lg (lg n)) ^ 2 / √(lg n)

lemma paperRate_le (n : ℕ) (hL : 0 < L n) (hl : 1 ≤ l n)
    (hoff : |Real.log (Real.log 2)| ≤ l n) :
    paperRate n ≤ (4 / (Real.log 2)^2) * alpha n := by
  let a := Real.log 2
  have ha : 0 < a := logTwo_pos
  have haux : lg (lg n) = (l n - Real.log a) / a := by
    unfold lg l L a
    rw [Real.log_div (show Real.log (n : ℝ) ≠ 0 from hL.ne') logTwo_pos.ne']
  have hden : √(L n) ≤ √(lg n) := Real.sqrt_le_sqrt
    ((le_div_iff₀ ha).mpr (by
      simpa [mul_one] using mul_le_mul_of_nonneg_left logTwo_le_one hL.le))
  have hnum : (lg (lg n))^2 ≤ (2 * l n / a)^2 := by
    rw [haux, div_pow, div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hab := abs_le.mp hoff
    have hs := abs_le.mpr (show -(2*l n) ≤ l n - Real.log a ∧ l n - Real.log a ≤ 2*l n by
      rcases hab with ⟨h₁, h₂⟩
      constructor <;> linarith)
    rw [← sq_abs (l n - Real.log a)]
    exact pow_le_pow_left₀ (abs_nonneg _) hs _
  unfold paperRate alpha beta
  calc
    _ ≤ (2 * l n / a)^2 / √(lg n) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (2 * l n / a)^2 / √(L n) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (Real.sqrt_pos.mpr hL) hden
    _ = _ := by dsimp [a]; ring

/-- F.A4 with B and κ fixed before the size threshold, quantified over every
layout, every window of size R and all executions with the three visit guarantees. -/
theorem FA4 (B κ : ℝ) (hB : 0 ≤ B) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, ∀ (copies Q r R q T : ℕ)
      (P : SlotLayout n copies Q r) (window : Finset ℕ),
      2 ≤ r → 0 < R → R < Q → window.card = R →
      (∀ u, (loadCell P u : ℝ) * cubeSize (Fin Q) (Fin r) ≤ 2 * (occupied P).card) →
      ((occupied P).card : ℝ) ≤ n * (lg n) ^ B →
      ⌊κ * (n : ℝ) * R / Q⌋₊ ≤ q →
      RoutineVisits P window q T →
      ((min κ 1 / 4096) * (Real.log 2)^2 / 4) * (n : ℝ) * paperRate n ≤ lg T := by
  let K := cutoffSlope B
  have hK : 256 ≤ K := by
    unfold K cutoffSlope
    exact le_add_of_nonneg_right (div_nonneg (by linarith) (neg_pos.mpr logXi_neg).le)
  have hK0 : 0 < K := by linarith
  let γ := min 1 (min (κ / (2*K)) (κ / 32))
  have hγ : 0 < γ := lt_min one_pos (lt_min (div_pos hκ (by positivity)) (div_pos hκ (by norm_num)))
  have hγ1 : γ ≤ 1 := min_le_left ..
  have hγ2 : γ ≤ κ / (2*K) := (min_le_right ..).trans (min_le_left ..)
  have hγ3 : γ ≤ κ / 32 := (min_le_right ..).trans (min_le_right ..)
  let δ := min κ 1 / 512
  have hδ : 0 < δ := div_pos (lt_min hκ one_pos) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ), tendsto_L.eventually_gt_atTop 0,
    tendsto_l.eventually_ge_atTop (max 1 (max (densityOffset B) |Real.log (Real.log 2)|)),
    eventually_alpha_times_l γ hγ, eventually_alpha_exp 1 (1/4) (by norm_num) (by norm_num),
    eventually_alpha_exp (Real.exp (-16)/16) (1/8) (by positivity) (by norm_num),
    eventually_n_beta 1, eventually_n_beta (2/δ), eventually_budget_offset B hB]
    with n hn hL hl' ha hb hc hd he hoff
  intro copies Q r R q T P window hr hR hQR hw hcap hM hq scan
  have hl : 1 ≤ l n := (le_max_left _ _).trans hl'
  have hOff : densityOffset B ≤ l n := (le_max_left _ _).trans ((le_max_right _ _).trans hl')
  have hlabs : |Real.log (Real.log 2)| ≤ l n := (le_max_right _ _).trans ((le_max_right _ _).trans hl')
  have hp := paperRate_le n hL hl hlabs
  have ha0 : 0 ≤ alpha n := by unfold alpha beta; positivity
  have ha' : alpha n ≤ γ := le_trans
    (by simpa using mul_le_mul_of_nonneg_right hl ha0) ha
  let M := (occupied P).card
  have hMp : 0 < M := by
    obtain ⟨x, hx⟩ := P.occurs ⟨0, by omega⟩
    exact Finset.card_pos.mpr ⟨x, by simp [occupied, hx]⟩
  have hlogM := log_M_le hMp hL B hM
  have hbudget : Real.log (2 * (M : ℝ)) ≤ 2 * L n := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hMp.ne')]
    unfold densityOffset at hoff
    linarith only [hlogM, hoff, logTwo_pos]
  have hs₆ : 2 ≤ δ * (n : ℝ) * beta n := by
    have hu := (div_le_iff₀ hδ).mp he
    linarith only [hu]
  have hna : 1 ≤ (n : ℝ) * alpha n := by
    unfold alpha
    nlinarith only [hd, mul_le_mul_of_nonneg_right hl (show 0 ≤ (n : ℝ) * beta n by linarith only [hd])]
  have hfa := FA4_at_size P window scan κ K hκ hK0 (by omega) hr hR hQR hw hL hl
    (by nlinarith only [hK, mul_le_mul_of_nonneg_left hl (show 0 ≤ K by linarith only [hK])])
    hna (ha'.trans hγ1) (by
      have := (le_div_iff₀ (show 0 < 2*K by positivity)).mp hγ2
      nlinarith only [this, mul_le_mul_of_nonneg_left ha (show 0 ≤ 2*K by positivity)])
    (by linarith only [ha'.trans hγ3]) (by simpa [div_eq_mul_inv] using hb)
    (by simpa [div_eq_mul_inv] using hc) hs₆ hq hcap hbudget
    (fun hq' => density_from_large_Q hMp hL hl B hB hOff hM hq')
  apply le_trans _ hfa
  have hc0 : 0 ≤ (min κ 1 / 4096) := by
    have hh := le_min hκ.le zero_le_one
    positivity
  have hpp := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (min κ 1 / 4096) * (Real.log 2)^2 / 4 * n by positivity)
  calc
    _ ≤ _ := hpp
    _ = _ := by field_simp [logTwo_pos.ne'] <;> ring

#print axioms density_from_large_Q
#print axioms paperRate_le
#print axioms FA4

end
end Section6



