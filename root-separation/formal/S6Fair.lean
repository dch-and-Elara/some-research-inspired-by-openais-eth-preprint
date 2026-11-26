import S6Orbit
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Section6

open Finset
open scoped BigOperators

noncomputable section

def fairMass (k j : ℕ) : ℝ := (k.choose j : ℝ) / 2 ^ k

def centralMass (m : ℕ) : ℝ := (m.centralBinom : ℝ) / 4 ^ m

lemma fairMass_nonneg (k j : ℕ) : 0 ≤ fairMass k j := by unfold fairMass; positivity

lemma centralMass_step (m : ℕ) :
    centralMass (m + 1) = centralMass m * (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) := by
  have he := Nat.succ_mul_centralBinom_succ m
  have hr : ((m : ℝ) + 1) * (↑((m + 1).centralBinom) : ℝ) =
      2 * (2 * (m : ℝ) + 1) * (m.centralBinom : ℝ) := by exact_mod_cast he
  rw [centralMass, centralMass, pow_succ]
  field_simp
  linarith

lemma centralMass_sq_lower (m : ℕ) :
    1 ≤ centralMass m ^ 2 * (4 * (m : ℝ) + 1) := by
  induction m with
  | zero => norm_num [centralMass]
  | succ m ih =>
    rw [centralMass_step, Nat.cast_succ, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < (2 * (m : ℝ) + 2)^2)]
    have h := mul_le_mul_of_nonneg_right ih (sq_nonneg (2 * (m : ℝ) + 2))
    have h0 : 0 ≤ centralMass m ^ 2 := sq_nonneg _
    nlinarith only [h, h0]

lemma inv_sqrt_le_centralMass (m : ℕ) :
    (√(4 * (m : ℝ) + 1))⁻¹ ≤ centralMass m := by
  have hp : 0 < √(4 * (m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 4 * (m : ℝ) + 1 by positivity)
  have he : 1 ≤ (centralMass m * √(4 * (m : ℝ) + 1)) ^ 2 := by
    rw [mul_pow, hs]
    exact centralMass_sq_lower m
  have hn : 0 ≤ centralMass m * √(4 * (m : ℝ) + 1) := by unfold centralMass; positivity
  rw [← one_div]
  apply (div_le_iff₀ hp).2
  by_contra! hh
  nlinarith [mul_pos (sub_pos.mpr hh) (show 0 < 1 + centralMass m * √(4 * (m : ℝ) + 1) by linarith)]

lemma fairMass_middle (k : ℕ) : 1 / (4 * √((k : ℝ) + 1)) ≤ fairMass k (k / 2) := by
  let m := k / 2
  have hmass : fairMass (2 * m) m = centralMass m := by
    unfold fairMass centralMass Nat.centralBinom
    rw [pow_mul]
    norm_num
  have hc : fairMass (2 * m) m ≤ 2 * fairMass (2 * m + 1) m := by
    unfold fairMass
    rw [pow_succ]
    have hn : (2 * m).choose m ≤ (2 * m + 1).choose m := Nat.choose_le_choose _ (Nat.le_succ _)
    have hr : ((2 * m).choose m : ℝ) ≤ ((2 * m + 1).choose m : ℝ) := by exact_mod_cast hn
    calc
      _ ≤ (((2 * m + 1).choose m : ℝ) / 2 ^ (2 * m)) := div_le_div_of_nonneg_right hr (by positivity)
      _ = _ := by ring
  have hn : 2 * m ≤ k := by dsimp [m]; omega
  have hs : √(4 * (m : ℝ) + 1) ≤ 2 * √((k : ℝ) + 1) := by
    have h := Real.sqrt_le_sqrt (show 4 * (m : ℝ) + 1 ≤ 4 * ((k : ℝ) + 1) by
      have hn' : (2 : ℝ) * m ≤ k := by exact_mod_cast hn
      linarith)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    exact h
  have hpos : 0 < √(4 * (m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hp : 0 < √((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hbase : 1 / (2 * √((k : ℝ) + 1)) ≤ fairMass (2 * m) m := by
    rw [hmass]
    exact (one_div_le_one_div_of_le hpos hs).trans (by simpa using inv_sqrt_le_centralMass m)
  change _ ≤ fairMass k m
  rcases (show k = 2 * m ∨ k = 2 * m + 1 by dsimp [m]; omega) with he | he
  · calc
      _ ≤ 1 / (2 * √((k : ℝ) + 1)) := one_div_le_one_div_of_le (by positivity) (by linarith)
      _ ≤ _ := hbase.trans_eq (congrArg (fun z => fairMass z m) he.symm)
  · have hh : 1 / (2 * √((k : ℝ) + 1)) ≤ 2 * fairMass k m := hbase.trans (by simpa only [← he] using hc)
    have hz : (1 / (4 * √((k : ℝ) + 1))) * 2 = 1 / (2 * √((k : ℝ) + 1)) := by ring
    linarith

lemma fairMass_step (k j : ℕ) (hj : j ≤ k) :
    fairMass k (j + 1) = fairMass k j * ((k : ℝ) - j) / (j + 1) := by
  have h := Nat.choose_succ_right_eq k j
  have hr : (k.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
      (k.choose j : ℝ) * ((k : ℝ) - j) := by exact_mod_cast h
  unfold fairMass
  field_simp
  exact hr

lemma shifted_mass (k d : ℕ) (hk : 0 < k) (hd : 8 * (k / 2 + d) ≤ 7 * k) :
    fairMass k (k / 2) * Real.exp (-(8 * (d : ℝ)^2 / k)) ≤ fairMass k (k / 2 + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hp : (0 : ℝ) < k := by exact_mod_cast hk
    have he : 8 * (k / 2 + d) ≤ 7 * k := by omega
    have hj : k / 2 + d ≤ k := by omega
    have hden : (k : ℝ) / 8 ≤ (k : ℝ) - (k / 2 + d : ℕ) := by
      have hr : (8 : ℝ) * (↑(k / 2 + d) : ℝ) ≤ 7 * (k : ℝ) := by exact_mod_cast he
      linarith
    have hj1 : 0 < ((k / 2 + d : ℕ) : ℝ) + 1 := by positivity
    have hden0 : 0 < (k : ℝ) - (k / 2 + d : ℕ) := by linarith
    have hnum : 2 * ((k / 2 + d : ℕ) : ℝ) + 1 - (k : ℝ) ≤ 2 * (d : ℝ) + 1 := by
      have hh : 2 * (k / 2) ≤ k := by omega
      have hh' : (2 : ℝ) * ((k / 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast hh
      push_cast
      linarith
    have hratio :
        Real.log (((k / 2 + d : ℕ) + 1 : ℝ) / ((k : ℝ) - (k / 2 + d : ℕ))) ≤
          (16 * (d : ℝ) + 8) / k := by
      apply (Real.log_le_sub_one_of_pos (show 0 < (((k / 2 + d : ℕ) + 1 : ℝ) /
          ((k : ℝ) - (k / 2 + d : ℕ))) by positivity)).trans
      rw [div_sub_one hden0.ne']
      have hid : ((k / 2 + d : ℕ) + 1 : ℝ) - ((k : ℝ) - (k / 2 + d : ℕ)) =
          2 * ((k / 2 + d : ℕ) : ℝ) + 1 - (k : ℝ) := by ring
      rw [hid]
      apply (div_le_div_of_nonneg_right hnum hden0.le).trans
      apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * (d : ℝ) + 1)
        (by positivity : 0 < (k : ℝ) / 8) hden).trans
      ring_nf
      rfl
    have hstep : Real.exp (-((16 * (d : ℝ) + 8) / k)) ≤
        ((k : ℝ) - (k / 2 + d : ℕ)) / ((k / 2 + d : ℕ) + 1 : ℝ) := by
      have hpos := div_pos hj1 hden0
      have he := Real.exp_le_exp.mpr hratio
      rw [Real.exp_log hpos] at he
      rw [Real.exp_neg]
      simpa only [inv_div] using (inv_le_inv₀ (Real.exp_pos _) hpos).2 he
    rw [show k / 2 + (d + 1) = (k / 2 + d) + 1 by omega, fairMass_step _ _ hj]
    have he' : -(8 * ((d + 1 : ℕ) : ℝ)^2 / k) =
        -(8 * (d : ℝ)^2 / k) + -((16 * (d : ℝ) + 8) / k) := by
      push_cast
      ring
    rw [he', Real.exp_add, ← mul_assoc]
    simpa only [← mul_div_assoc] using mul_le_mul (ih he) hstep (Real.exp_nonneg _) (fairMass_nonneg _ _)

lemma fairTail_cast (k : ℕ) (window : Finset ℕ) :
    (fairTail k window : ℝ) = ∑ j ∈ (range (k + 1)).filter (· ∉ window), fairMass k j := by
  simp [fairTail, fairMass, sum_div]

/-- F.A2 with explicit constants, for every set of R weights. -/
theorem FA2 (Q k R : ℕ) (window : Finset ℕ) (hQ : 256 ≤ Q)
    (hk₁ : Q ≤ 4 * k) (_hk₂ : k ≤ Q) (hR : 16 * R ≤ Q) (hw : window.card = R) :
    (Real.exp (-16) / 8) * Real.exp (-(64 * (R : ℝ)^2 / Q)) ≤ (fairTail k window : ℝ) := by
  let s := Nat.sqrt k
  let block := Ico (k / 2) (k / 2 + (R + s))
  have hk : 64 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hs : 8 ≤ s := Nat.le_sqrt'.mpr (by omega)
  have hs2 : s ^ 2 ≤ k := Nat.sqrt_le' k
  have hss : 8 * s ≤ k := (Nat.mul_le_mul_right s hs).trans (Nat.sqrt_le k)
  have hblock : 8 * (k / 2 + (R + s)) ≤ 7 * k := by omega
  have hcount : s ≤ (block \ window).card := by
    have hc := card_sdiff_add_card_inter block window
    have hb : block.card = R + s := by simp [block]
    have hi : (block ∩ window).card ≤ R := hw ▸ card_le_card (inter_subset_right : block ∩ window ⊆ window)
    omega
  have hsqr : √((k : ℝ) + 1) ≤ 2 * (s : ℝ) := by
    have hsn : k + 1 ≤ (s + 1)^2 := by exact Nat.succ_le_of_lt (Nat.lt_succ_sqrt' k)
    have hsn' : (k : ℝ) + 1 ≤ ((s : ℝ) + 1)^2 := by exact_mod_cast hsn
    have hh := Real.sqrt_le_sqrt hsn'
    rw [Real.sqrt_sq (by positivity)] at hh
    have hs' : (8 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hloc (j : ℕ) (hj : j ∈ block \ window) :
      (1 / (8 * (s : ℝ))) * Real.exp (-(16 + 64 * (R : ℝ)^2 / Q)) ≤ fairMass k j := by
    have hmem : k / 2 ≤ j ∧ j < k / 2 + (R + s) := mem_Ico.mp (mem_sdiff.mp hj).1
    let d := j - k / 2
    have he : k / 2 + d = j := Nat.add_sub_of_le hmem.1
    have hd : d ≤ R + s := by omega
    have hstep := shifted_mass k d (by omega) (by omega)
    rw [he] at hstep
    apply le_trans _ hstep
    apply mul_le_mul
    · exact (one_div_le_one_div_of_le (by positivity)
        (show 4 * √((k : ℝ) + 1) ≤ 8 * (s : ℝ) by linarith)).trans (fairMass_middle k)
    · apply Real.exp_le_exp.mpr
      have hd' : (d : ℝ) ≤ (R : ℝ) + s := by exact_mod_cast hd
      have hs2' : (s : ℝ)^2 ≤ k := by exact_mod_cast hs2
      have hsle : (d : ℝ)^2 ≤ 2 * (R : ℝ)^2 + 2 * k := by
        nlinarith [sq_nonneg ((R : ℝ) - (s : ℝ)),
          mul_nonneg (sub_nonneg.mpr hd') (show 0 ≤ (R : ℝ) + s + d by positivity)]
      have hdiv : 8 * (d : ℝ)^2 / k ≤ 16 + 16 * (R : ℝ)^2 / k := by
        apply (div_le_iff₀ hk0).2
        calc
          _ ≤ 16 * (R : ℝ)^2 + 16 * k := by linarith
          _ = _ := by field_simp; ring
      have hQk : (Q : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast hk₁
      have hr : 16 * (R : ℝ)^2 / k ≤ 64 * (R : ℝ)^2 / Q := by
        rw [div_le_div_iff₀ hk0 hQ0]
        nlinarith [mul_nonneg (sub_nonneg.mpr hQk) (sq_nonneg (R : ℝ))]
      linarith
    · positivity
    · exact fairMass_nonneg _ _
  have hsub : block \ window ⊆ (range (k + 1)).filter (· ∉ window) := by
    intro j hj
    have hmem : k / 2 ≤ j ∧ j < k / 2 + (R + s) := mem_Ico.mp (mem_sdiff.mp hj).1
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), (mem_sdiff.mp hj).2⟩
  rw [fairTail_cast]
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => fairMass_nonneg _ _))
  have hsum := sum_le_sum (s := block \ window) hloc
  rw [sum_const, nsmul_eq_mul] at hsum
  have hcount' : (s : ℝ) ≤ (block \ window).card := by exact_mod_cast hcount
  apply le_trans _ ((mul_le_mul_of_nonneg_right hcount' (by positivity)).trans hsum)
  rw [neg_add, Real.exp_add]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  field_simp; ring_nf; norm_num

#print axioms centralMass_sq_lower
#print axioms shifted_mass
#print axioms FA2

end
end Section6





