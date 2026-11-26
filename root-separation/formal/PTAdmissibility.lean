import PTThreshold

namespace RootSeparation.Preprocessing

open S11

theorem linear_le_twoPow_div (l : ℕ) (hl : 1024 ≤ l) :
    l ≤ 2^(l/32) := by
  have h (g : ℕ) : 32*(g+11) ≤ 2^(g+10) := by
    induction g with
    | zero => decide
    | succ g ih =>
      rw [show g+1+10 = g+10+1 by omega, pow_succ]
      omega
  have hdiv := Nat.mod_add_div l 32
  have hmod := Nat.mod_lt l (by decide : 0 < 32)
  have hk : l/32-10+10 = l/32 := by omega
  have hs := h (l/32-10)
  rw [hk] at hs
  have hu : l ≤ 32*(l/32-10+11) := by
    -- Convert to the unshifted bound supplied by the induction below.
    clear hs
    omega
  exact hu.trans hs

lemma active_wire_lower {s M : ℕ} (hl : 1024 ≤ lambda s) (ha : leafThreshold s < M) :
    2^(lambda s-1-lambda s/32) < M := by
  let l := lambda s
  let j := l-1-l/32
  let b := l.sqrt
  have hl' : 1024 ≤ l := hl
  have hl0 : 0 < l := by omega
  have hb : 0 < b := Nat.sqrt_pos.mpr hl0
  have hsize : s ≤ leafThreshold s*b := ceil_le_product _ _ hb
  have hM : s < M*b := hsize.trans_lt (Nat.mul_lt_mul_of_pos_right ha hb)
  have hs : b ≤ 2^(l/32) := (Nat.sqrt_le_self l).trans (linear_le_twoPow_div l hl')
  have hj : j+l/32 = l-1 := by unfold j; omega
  have hh : 2^j * 2^(l/32) < M*2^(l/32) := by
    rw [← pow_add,hj]
    exact (logWindow hl0).1.trans (hM.trans_le (Nat.mul_le_mul_left _ hs))
  exact Nat.lt_of_mul_lt_mul_right hh

/-- The checks needed by the active contraction, plus the source dimension
and retained-power estimates. The graph degree invariant is supplied by
the inherited vertices and the bound on new packet port count. -/
structure ActiveNumbers (s d M : ℕ) : Prop where
  retainedPos : 0 < retained s d
  retainedLeLabel : retained s d ≤ labelLength s d
  retainedLeWire : retained s d ≤ M
  retainedPower : lambda s^4 ≤ retained s d ^ 5
  labelCap : 131072*labelLength s d ≤ 4*lambda s
  packetCap : packetLength s d ^ 1000 ≤ s
  arrayCap : arrayCells s d ^ 1000 ≤ s
  degreeCover : 3 ≤ degreeEnvelope s
  collisionPacking : 2*(arrayCells s d)^2*degreeEnvelope s ≤ M
  enoughSlots : packetLength s d * arrayCells s d ≤ M
  packetPorts : 2*packetLength s d ≤ degreeEnvelope s
  probeBudget : probeCount M (packetLength s d) < s^4
  probeCapacity : probeCount M (packetLength s d) ≤ 2^(4*lambda s)

/-- The actual active numerical checks eventually pass simultaneously,
even if the root fallback checks every reachable active depth. -/
theorem active_numbers {s d M : ℕ}
    (hcut : depthLogCutoff ≤ lambda s)
    (ha : leafThreshold s < M) (hshrink : M*8^d ≤ 3*s) :
    ActiveNumbers s d M := by
  let l := lambda s
  let a := labelLength s d
  let u := retained s d
  let L := packetLength s d
  let D := arrayCells s d
  let j := l-1-l/32
  let b := (9*l+9)/10
  have hl : 131072 ≤ l := depthLogCutoff_large.trans hcut
  have hl0 : 0 < l := by omega
  have hWin := logWindow hl0
  have hMlower : 2^j < M := active_wire_lower (by omega : 1024 ≤ l) ha
  have hMupper : M ≤ 3*s :=
    (Nat.le_mul_of_pos_right _ (by positivity : 0 < (8:ℕ)^d)).trans hshrink
  have hPow := active_retained_power hcut ha hshrink
  change l^4 ≤ u^5 at hPow
  have hu : 0 < u := by
    by_contra! h
    simp [show u=0 by omega] at hPow
    omega
  have hau : 2*u ≤ a := by
    unfold a labelLength
    exact Nat.mul_le_mul_left _ (Finset.single_le_sum (f := fun j => retained s j) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr d.lt_succ_self))
  have haUpper : 131072*a ≤ 4*l := by
    have hh := Nat.mul_le_mul_left 131072 (label_upper s d)
    have hu0 : 131072*retained s 0 ≤ l := by
      simpa [retained,l] using Nat.mul_div_le l 131072
    omega
  have huJ : u ≤ j := by
    have ht : 131072*u ≤ l :=
      (Nat.mul_le_mul_left 131072 (retained_upper s d)).trans (by
        simpa [retained,l] using Nat.mul_div_le l 131072)
    unfold j
    omega
  obtain ⟨hD,hLD,hDD⟩ := array_powers s d
  change D = 2^(12*a) at hD
  change L*D = 2^(13*a) at hLD
  change 2*D^2 = 2^(24*a+1) at hDD
  have hL : L = 2^a := rfl
  have hLP : L^1000 ≤ s := by
    rw [hL, ← pow_mul]
    exact (Nat.pow_le_pow_right (by decide) (show a*1000 ≤ l-1 by omega)).trans hWin.1.le
  have hDP : D^1000 ≤ s := by
    rw [hD, ← pow_mul]
    exact (Nat.pow_le_pow_right (by decide) (show (12*a)*1000 ≤ l-1 by omega)).trans hWin.1.le
  have hΔupper : degreeEnvelope s ≤ 2^b := by
    apply degree_le
    calc
      _ ≤ (2^l)^9 := Nat.pow_le_pow_left hWin.2 _
      _ ≤ (2^b)^10 := by
        rw [← pow_mul, ← pow_mul]
        apply Nat.pow_le_pow_right (by decide)
        unfold b
        omega
  have hΔlower : 2^(a+1) ≤ degreeEnvelope s := by
    by_contra! h
    have hw := Nat.pow_lt_pow_left h (by decide : (10:ℕ) ≠ 0)
    have hp : (2^(a+1):ℕ)^10 ≤ (2^(l-1))^9 := by
      rw [← pow_mul, ← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (not_lt_of_ge ((hp.trans (Nat.pow_le_pow_left hWin.1.le 9)).trans (degree_valid s))) hw
  have h3 : 3 ≤ degreeEnvelope s :=
    (show (3:ℕ) ≤ 2^2 by decide).trans ((Nat.pow_le_pow_right (by decide)
      (show 2 ≤ a+1 by omega)).trans hΔlower)
  have hp1 : 2*D^2*degreeEnvelope s ≤ M := by
    rw [hDD]
    calc
      _ ≤ 2^(24*a+1)*2^b := Nat.mul_le_mul_left _ hΔupper
      _ ≤ 2^j := by
        rw [← pow_add]
        apply Nat.pow_le_pow_right (by decide)
        unfold b j
        omega
      _ ≤ M := hMlower.le
  have hp2 : L*D ≤ M := by
    rw [hLD]
    exact (Nat.pow_le_pow_right (by decide) (show 13*a ≤ j by unfold j; omega)).trans hMlower.le
  have hp3 : 2*L ≤ degreeEnvelope s := by
    rw [hL]
    simpa only [pow_succ, Nat.mul_comm 2] using hΔlower
  have hMu : M ≤ 2^(l+2) := by
    calc
      _ ≤ 3*2^l := hMupper.trans (Nat.mul_le_mul_left _ hWin.2)
      _ ≤ _ := by rw [pow_add]; omega
  let e := l+2+(a+1)
  have hProbe : probeCount M L ≤ 2^(e+1) := by
    have h := Nat.mul_le_mul hMu (show 2*L-1 ≤ 2^(a+1) by rw [hL, pow_succ]; omega)
    rw [← pow_add] at h
    have hPos : 0 < 2^e := by positivity
    unfold probeCount
    rw [pow_succ]
    change M*(2*L-1) + 1 ≤ 2^e*2
    change M*(2*L-1) ≤ 2^e at h
    omega
  have hPb : 2^(e+1) ≤ (2^(l-1):ℕ)^4 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by unfold e; omega)
  have hProbeSize : probeCount M L < s^4 :=
    (hProbe.trans hPb).trans_lt (Nat.pow_lt_pow_left hWin.1 (by decide))
  have hProbeCap : probeCount M L ≤ 2^(4*l) := by
    exact hProbe.trans (Nat.pow_le_pow_right (by decide) (by unfold e; omega))
  exact ⟨hu,by omega, huJ.trans (Nat.lt_two_pow_self.le.trans hMlower.le), hPow,
    haUpper,hLP,hDP,h3,hp1,hp2,hp3,hProbeSize,hProbeCap⟩

#print axioms active_numbers

end RootSeparation.Preprocessing

