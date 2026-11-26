import RootParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RootSeparation.Preprocessing

open S11 Finset
open scoped BigOperators

/-- A sufficient uniform threshold on lambda for the source
lambda^(4/5) estimate on every active depth with M * 8^d <= 3s. -/
def depthLogCutoff : ℕ := 262144^30 * 9^5

def arrayCells (s d : ℕ) : ℕ := 64^(2*labelLength s d)

theorem depthLogCutoff_large : 131072 ≤ depthLogCutoff := by
  unfold depthLogCutoff
  have h₁ : 262144 ≤ (262144:ℕ)^30 := by
    decide
  exact (by decide : 131072 ≤ 262144).trans (h₁.trans (Nat.le_mul_of_pos_right _ (by positivity)))

lemma logWindow {s : ℕ} (hl : 0 < lambda s) :
    2^(lambda s-1) < s ∧ s ≤ 2^lambda s := by
  constructor
  · exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp (by
      change lambda s-1 < lambda s
      omega)
  · exact Nat.le_pow_clog (by decide : 1 < 2) s

lemma ceil_le_product (a b : ℕ) (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  have hr := Nat.mod_lt (a+b-1) hb
  have he := Nat.mod_add_div (a+b-1) b
  unfold ceilDiv
  rw [Nat.mul_comm _ b]
  omega

lemma label_succ (s d : ℕ) :
    labelLength s (d+1) = labelLength s d + 2*retained s (d+1) := by
  unfold labelLength
  rw [sum_range_succ,mul_add]

lemma retained_step (s d : ℕ) : 2 * retained s (d+1) ≤ retained s d := by
  unfold retained
  rw [pow_succ, ← mul_assoc, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

lemma retained_upper (s d : ℕ) : retained s d ≤ retained s 0 := by
  unfold retained
  simp only [pow_zero,mul_one]
  exact Nat.div_le_div_left (Nat.le_mul_of_pos_right _ (by positivity)) (by decide)

theorem label_upper (s d : ℕ) : labelLength s d ≤ 4*retained s 0 := by
  have h (d : ℕ) : labelLength s d + 2*retained s d ≤ 4*retained s 0 := by
    induction d with
    | zero => have := (root_parameters s).1; omega
    | succ d ih =>
      rw [label_succ]
      have := retained_step s d
      omega
  have := h d
  omega

lemma array_powers (s d : ℕ) :
    arrayCells s d = 2^(12*labelLength s d) ∧
    packetLength s d * arrayCells s d = 2^(13*labelLength s d) ∧
    2*arrayCells s d ^ 2 = 2^(24*labelLength s d+1) := by
  let a := labelLength s d
  have he : arrayCells s d = 2^(12*a) := by
    unfold arrayCells
    rw [show (64:ℕ) = 2^6 by decide, ← pow_mul]
    congr 1
    omega
  rw [he]
  change 2^(12*a) = _ ∧ 2^a * 2^(12*a) = _ ∧ _
  refine ⟨rfl,?_,?_⟩
  · rw [← pow_add]; congr 1; omega
  · change 2*(2^(12*a):ℕ)^2 = 2^(24*a+1)
    rw [← pow_mul, show 12*a*2 = 24*a by omega, pow_succ, Nat.mul_comm 2]

lemma active_depth_power {s d M : ℕ}
    (hl : 0 < lambda s) (ha : leafThreshold s < M) (hd : M*8^d ≤ 3*s) :
    (2^d)^6 ≤ 9*lambda s := by
  let l := lambda s
  let b := l.sqrt
  let p := (2:ℕ)^d
  have hb : 0 < b := Nat.sqrt_pos.mpr hl
  have hs : 0 < s := lt_of_lt_of_le (by positivity) (logWindow hl).1.le
  have hA : s ≤ leafThreshold s*b := ceil_le_product _ _ hb
  have hB : s < M*b := hA.trans_lt (Nat.mul_lt_mul_of_pos_right ha hb)
  have hp : 0 < p := by positivity
  have hp3 : p^3 = 8^d := by
    dsimp [p]
    rw [← pow_mul, mul_comm d 3, pow_mul]
    norm_num
  have hC : s*p^3 < (3*b)*s := by
    calc
      _ < (M*b)*p^3 := Nat.mul_lt_mul_of_pos_right hB (by positivity)
      _ = (M*8^d)*b := by rw [hp3]; ring
      _ ≤ (3*s)*b := Nat.mul_le_mul_right _ hd
      _ = _ := by ring
  have hD : p^3 ≤ 3*b := Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right (by
    simpa [Nat.mul_comm s (p^3)] using hC))
  have hE := Nat.pow_le_pow_left hD 2
  change p^6 ≤ 9*l
  rw [show (6:ℕ) = 3*2 by decide, pow_mul]
  exact hE.trans (by rw [mul_pow]; exact Nat.mul_le_mul_left _ (Nat.sqrt_le' l))

/-- Integer form of the 4/5-power lower estimate, uniform at all active
sizes along the proven edge-shrink invariant. -/
theorem active_retained_power {s d M : ℕ}
    (hcut : depthLogCutoff ≤ lambda s)
    (ha : leafThreshold s < M) (hd : M*8^d ≤ 3*s) :
    lambda s^4 ≤ (retained s d)^5 := by
  let l := lambda s
  let p := (2:ℕ)^d
  let B := 131072*p
  let A := 2*B
  let u := l/B
  have hl : 0 < l := (by decide : 0 < 131072).trans_le (depthLogCutoff_large.trans hcut)
  have hB : 0 < B := by unfold B p; positivity
  have hA : 0 < A := by unfold A; positivity
  have hp := active_depth_power hl ha hd
  have he : A^30 ≤ l^6 := by
    have hrepr : A = 262144*p := by unfold A B; ring
    rw [hrepr, mul_pow, show (30:ℕ)=6*5 by decide, pow_mul p 6 5]
    calc
      _ ≤ (262144:ℕ)^(6*5)*(9*l)^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 5)
      _ = depthLogCutoff * l^5 := by unfold depthLogCutoff; rw [mul_pow]; ring
      _ ≤ l*l^5 := Nat.mul_le_mul_right _ hcut
      _ = _ := (pow_succ' l 5).symm
  have hAl : A^5 ≤ l := by
    by_contra! h
    have hh := Nat.pow_lt_pow_left h (by decide : (6:ℕ) ≠ 0)
    rw [← pow_mul] at hh
    exact (not_lt_of_ge he) hh
  have h1 : 1 ≤ u := by
    apply (Nat.le_div_iff_mul_le hB).mpr
    have hAB : B ≤ A := by unfold A; omega
    have hAA : A ≤ A^5 := by simpa using Nat.pow_le_pow_right hA (by decide : 1 ≤ 5)
    simpa using hAB.trans (hAA.trans hAl)
  have hq : l < (u+1)*B := by
    simpa [u,Nat.mul_comm B] using Nat.lt_mul_div_succ l hB
  have hh : l ≤ A*u := by
    have h := Nat.mul_le_mul_right B (show u+1 ≤ 2*u by omega)
    exact hq.le.trans (h.trans_eq (by unfold A; ring))
  have hn : l^5 ≤ l*u^5 := by
    calc
      _ ≤ (A*u)^5 := Nat.pow_le_pow_left hh _
      _ ≤ l*u^5 := by rw [mul_pow]; exact Nat.mul_le_mul_right _ hAl
  have hu : retained s d = u := rfl
  rw [hu]
  rw [pow_succ] at hn
  exact Nat.le_of_mul_le_mul_right (by simpa [mul_comm l (u^5)] using hn) hl

theorem active_retained_rpow {s d M : ℕ}
    (hcut : depthLogCutoff ≤ lambda s)
    (ha : leafThreshold s < M) (hd : M*8^d ≤ 3*s) :
    (lambda s : ℝ) ^ (4/5 : ℝ) ≤ (retained s d : ℝ) := by
  have h := active_retained_power hcut ha hd
  have hx : (0 : ℝ) ≤ (lambda s : ℝ) ^ (4/5 : ℝ) := by positivity
  have hy : (0 : ℝ) ≤ (retained s d : ℝ) := by positivity
  apply (pow_le_pow_iff_left₀ hx hy (by decide : 5 ≠ 0)).mp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    show (4/5:ℝ) * ((5:ℕ):ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  exact_mod_cast h

#print axioms active_depth_power
#print axioms label_upper
#print axioms active_retained_power
#print axioms active_retained_rpow

end RootSeparation.Preprocessing


