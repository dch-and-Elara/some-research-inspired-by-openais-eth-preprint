import SolverLayout

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial

private theorem pow2_le {a b : ℕ} (h : a ≤ b) : (2:ℕ)^a ≤ 2^b :=
  Nat.pow_le_pow_right (by decide) h

private theorem retained_next (s d : ℕ) : 2 * retained s (d+1) ≤ retained s d := by
  have hd : retained s (d+1) = retained s d / 2 := by
    unfold retained
    rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_assoc]
  rw [hd,Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

private theorem labelLength_bound (s d : ℕ) :
    131072 * labelLength s d ≤ 4 * lambda s := by
  have hsum (i : ℕ) : (∑ j ∈ Finset.range (i+1), retained s j) + retained s i ≤
      2 * retained s 0 := by
    induction i with
    | zero => simp [two_mul]
    | succ i hi =>
      rw [Finset.sum_range_succ]
      have h := retained_next s i
      omega
  have h : 131072 * retained s 0 ≤ lambda s := by
    simpa only [retained,pow_zero,mul_one] using Nat.mul_div_le (lambda s) 131072
  have hh := Nat.mul_le_mul_left 131072 (hsum d)
  rw [Nat.mul_add, ← Nat.mul_assoc, show (131072:ℕ)*2 = 262144 by decide] at hh
  change 131072 * (2 * ∑ j ∈ Finset.range (d+1), retained s j) ≤ _
  rw [← Nat.mul_assoc,show (131072:ℕ)*2=262144 by decide]
  omega

private theorem twenty_mul_le_pow (k : ℕ) (h : 10 ≤ k) : 20*(k+1) ≤ 2^k := by
  induction k, h using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ]
    omega

private theorem sqrt_le_dyadic (l : ℕ) (hl : 200 ≤ l) :
    Nat.sqrt l ≤ 2^(l/20) := by
  have h : 10 ≤ l/20 := by omega
  exact (Nat.sqrt_le_self l).trans ((show l ≤ 20*(l/20+1) by omega).trans
    (twenty_mul_le_pow _ h))

private theorem ceil_mul_ge (s r : ℕ) (hr : 0 < r) : s ≤ r * ceilDiv s r := by
  have hmod := Nat.mod_lt (s+r-1) hr
  have he := Nat.mod_add_div (s+r-1) r
  unfold ceilDiv
  omega

private theorem cellCount (a : ℕ) : Fintype.card (RootCell a) = 2^(12*a) := by
  simp only [RootCell,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,← pow_add]
  rw [show (64:ℕ) = 2^6 by decide, ← pow_mul]
  congr 1
  omega

/-- All numerical tests for every reached active call, using a deliberately
    coarse fixed finite cutoff. The invariant is physical wire shrink. -/
theorem active_numeric (s d M : ℕ)
    (hl : 2^40 ≤ lambda s) (hdepth : 8^d * M ≤ 3*s) (hactive : leafThreshold s < M) :
    0 < retained s d ∧ retained s d ≤ M ∧
    2 * Fintype.card (RootCell (labelLength s d))^2 * degreeEnvelope s ≤ M ∧
    packetLength s d * Fintype.card (RootCell (labelLength s d)) ≤ M ∧
    2 * packetLength s d ≤ degreeEnvelope s ∧
    probeCount M (packetLength s d) ≤ 2^(4*lambda s) := by
  let l := lambda s
  let a := labelLength s d
  let r := Nat.sqrt l
  let k := l/20
  let b := (9*l+9)/10
  have hr : 0 < r := Nat.sqrt_pos.2 (by dsimp [l]; omega)
  have hhi : s ≤ 2^l := (Nat.clog_le_iff_le_pow (by decide : 1<2)).1 le_rfl
  have hlo : 2^(l-1) < s := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).1 (by
    show l-1 < l
    have h : 0 < l := by dsimp [l]; omega
    omega)
  have hsa : s < r*M := (ceil_mul_ge s r hr).trans_lt (Nat.mul_lt_mul_of_pos_left hactive hr)
  have hscale : 8^d < 3*r := by
    have h := hdepth.trans_lt (Nat.mul_lt_mul_of_pos_left hsa (by decide : 0 < 3))
    rw [← Nat.mul_assoc] at h
    exact Nat.lt_of_mul_lt_mul_right h
  have h2d : 2^d ≤ 3*r := (Nat.pow_le_pow_left (by decide : 2 ≤ 8) d).trans hscale.le
  have hr2 : r*r ≤ l := by simpa only [pow_two] using Nat.sqrt_le' l
  have hlr : 393216 ≤ r := by
    apply Nat.le_sqrt.2
    dsimp [l]
    exact (show 393216*393216 ≤ 2^40 by decide).trans hl
  have hd2 : 131072 * 2^d ≤ l := by
    calc
      _ ≤ 131072 * (3*r) := Nat.mul_le_mul_left _ h2d
      _ = 393216*r := by ring
      _ ≤ r*r := Nat.mul_le_mul_right _ hlr
      _ ≤ l := hr2
  have hu : 0 < retained s d := Nat.div_pos hd2 (by positivity)
  have ha : 131072*a ≤ 4*l := labelLength_bound s d
  have hb : 9*l ≤ 10*b := by dsimp [b]; omega
  have hΔup : degreeEnvelope s ≤ 2^b := by
    apply degree_le
    calc
      s^9 ≤ (2^l)^9 := Nat.pow_le_pow_left hhi _
      _ ≤ (2^b)^10 := by rw [← pow_mul,← pow_mul]; apply pow2_le; omega
  have hΔlo : 2^(a+1) ≤ degreeEnvelope s := by
    by_contra! hn
    apply (not_lt_of_ge (degree_valid s))
    calc
      (degreeEnvelope s)^10 < (2^(a+1))^10 := Nat.pow_lt_pow_left hn (by decide)
      _ ≤ (2^(l-1))^9 := by rw [← pow_mul,← pow_mul]; apply pow2_le; omega
      _ ≤ s^9 := Nat.pow_le_pow_left hlo.le _
  have hmlo : 2^(l-1-k) < M := by
    have hk : r ≤ 2^k := sqrt_le_dyadic l (by dsimp [l]; omega)
    have h := hlo.trans_le (hsa.le.trans (Nat.mul_le_mul_right _ hk))
    rw [← show k+(l-1-k)=l-1 by dsimp [k]; omega, pow_add] at h
    exact Nat.lt_of_mul_lt_mul_left h
  have huM : retained s d ≤ M := by
    have hu' : retained s d ≤ l := Nat.div_le_self _ _
    have hlm : l ≤ 2^(l-1-k) := by
      have hh := twenty_mul_le_pow k (by dsimp [k,l]; omega)
      exact (show l ≤ 20*(k+1) by dsimp [k]; omega).trans
        (hh.trans (pow2_le (by dsimp [k]; omega)))
    exact hu'.trans (hlm.trans hmlo.le)
  have hMhi : M ≤ 2^(l+2) := by
    have hM : M ≤ 3*s :=
      (show M ≤ 8^d * M from Nat.le_mul_of_pos_left _ (by positivity)).trans hdepth
    calc
      M ≤ 3*s := hM
      _ ≤ 4*2^l := by omega
      _ = 2^(l+2) := by rw [pow_add]; ring
  refine ⟨hu,huM,?_,?_,?_,?_⟩
  · rw [cellCount, ← pow_mul]
    change 2 * 2^(12*a*2) * degreeEnvelope s ≤ M
    calc
      _ ≤ 2 * 2^(12*a*2) * 2^b := Nat.mul_le_mul_left _ hΔup
      _ ≤ 2^(l-1-k) := by
        rw [← pow_succ', ← pow_add]
        apply pow2_le
        dsimp [k,b]
        omega
      _ ≤ M := hmlo.le
  · rw [cellCount]
    change 2^a * 2^(12*a) ≤ M
    rw [← pow_add]
    exact (pow2_le (by dsimp [k]; omega)).trans hmlo.le
  · exact (show 2 * 2^a ≤ degreeEnvelope s by rw [← pow_succ']; exact hΔlo)
  · have hb' : M*(2*2^a-1) ≤ 2^(l+2)*2^(a+1) := by
      apply Nat.mul_le_mul hMhi
      rw [pow_succ']
      omega
    rw [← pow_add] at hb'
    have h := Nat.pow_lt_pow_right (by decide : 1 < 2) (show l+2+(a+1) < 4*l by omega)
    change M*(2*2^a-1)+1 ≤ 2^(4*l)
    omega

#print axioms active_numeric

end RootSeparation.Solver
