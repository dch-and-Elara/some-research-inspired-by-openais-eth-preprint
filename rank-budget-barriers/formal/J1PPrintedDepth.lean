import J9PrintedSchedule

/-! Exact all-depth arithmetic of Appendix D, source lines 81–108.
All floors and the active leaf test are retained. The very conservative
size threshold for the exponent 4/5 is explicit and depends only on C. -/

namespace J1PPrinted

open scoped BigOperators

def epsDen : ℕ := 128*1024

def stepU (lambda d : ℕ) : ℕ := lambda / (epsDen * 2^d)

def stepA (lambda d : ℕ) : ℕ := 2 * ∑ j ∈ Finset.range (d+1), stepU lambda j

def stepL (lambda d : ℕ) : ℕ := 2^stepA lambda d

def stepD (lambda d : ℕ) : ℕ := J9PrintedSchedule.arrayCard (stepA lambda d)

theorem stepU_as_div (lambda d : ℕ) :
    stepU lambda d = J9PrintedSchedule.rootU lambda / 2^d := by
  rw [stepU, J9PrintedSchedule.rootU, epsDen, Nat.div_div_eq_div_mul]

theorem stepU_succ (lambda d : ℕ) : stepU lambda (d+1) = stepU lambda d / 2 := by
  rw [stepU_as_div, stepU_as_div, pow_succ, Nat.div_div_eq_div_mul]

theorem depth_geom (lambda d : ℕ) :
    (∑ j ∈ Finset.range (d+1), stepU lambda j) + stepU lambda d ≤
      2*J9PrintedSchedule.rootU lambda := by
  induction d with
  | zero => simp [stepU_as_div,two_mul]
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have hu : 2*stepU lambda (d+1) ≤ stepU lambda d := by
      rw [stepU_succ, Nat.mul_comm]
      exact Nat.div_mul_le_self _ _
    omega

theorem stepA_bound (lambda d : ℕ) : stepA lambda d ≤ 4*J9PrintedSchedule.rootU lambda := by
  have h := depth_geom lambda d
  unfold stepA
  omega

theorem stepA_has_u (lambda d : ℕ) : stepU lambda d ≤ stepA lambda d := by
  have h : stepU lambda d ≤ ∑ j ∈ Finset.range (d+1), stepU lambda j :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (stepU lambda i))
      (Finset.mem_range.mpr (Nat.lt_succ_self d))
  unfold stepA
  omega

theorem stepD_power (lambda d : ℕ) : stepD lambda d = (stepL lambda d)^12 :=
  J9PrintedSchedule.arrayCard_power _

theorem active_wire_lower (s M : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M) :
    (2:ℕ)^(Nat.clog 2 s - 18 - J9PrintedSchedule.rootU (Nat.clog 2 s)) < M := by
  let lambda := Nat.clog 2 s
  let u := J9PrintedSchedule.rootU lambda
  have hu : 1 ≤ u := hU
  have h := J9PrintedSchedule.rootU_range lambda
  change 131072*u ≤ lambda ∧ lambda < 131072*(u+1) at h
  have hp : 0 < lambda := by omega
  have hroot : 0 < lambda.sqrt := Nat.sqrt_pos.mpr hp
  have hlog : lambda ≤ (2:ℕ)^(17+u) := by
    calc
      lambda ≤ 131072*(u+1) := h.2.le
      _ ≤ 131072*2^u := Nat.mul_le_mul_left _ (J9PrintedSchedule.next_le_two_power u)
      _ = _ := (pow_add 2 17 u).symm
  have hcalc : (2:ℕ)^(lambda-18-u) * lambda.sqrt ≤ 2^(lambda-1) := by
    calc
      _ ≤ (2:ℕ)^(lambda-18-u) * 2^(17+u) :=
        Nat.mul_le_mul_left _ ((Nat.sqrt_le_self _).trans hlog)
      _ = 2^((lambda-18-u)+(17+u)) := (pow_add _ _ _).symm
      _ = 2^(lambda-1) := by congr 1; omega
  have hlt : (2:ℕ)^(lambda-1) < s :=
    (Nat.lt_clog_iff_pow_lt (b:=2) (by decide)).1 (by change lambda-1<lambda; omega)
  have hhi : s ≤ M * lambda.sqrt :=
    (J9PrintedSchedule.le_roundup_mul s lambda.sqrt hroot).trans
      (Nat.mul_le_mul_right _ active.le)
  exact Nat.lt_of_mul_lt_mul_right ((hcalc.trans_lt hlt).trans_le hhi)

/-- The actual factor-eight shrink bound gives a certified depth budget,
without any hidden O_C(1). -/
theorem depth_sixth_bound (s M C d : ℕ)
    (hlambda : 0 < Nat.clog 2 s)
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (shrink : 8^d*M ≤ C*s) :
    ((2:ℕ)^d)^6 ≤ C^2 * Nat.clog 2 s := by
  let lambda := Nat.clog 2 s
  have hR : 0 < lambda.sqrt := Nat.sqrt_pos.mpr hlambda
  have hM : 0 < M := Nat.zero_lt_of_lt active
  have hs : s ≤ M*lambda.sqrt :=
    (J9PrintedSchedule.le_roundup_mul s lambda.sqrt hR).trans
      (Nat.mul_le_mul_right _ active.le)
  have h8 : 8^d ≤ C*lambda.sqrt := by
    have hmul : 8^d*M ≤ (C*lambda.sqrt)*M := by
      calc
        8^d*M ≤ C*s := shrink
        _ ≤ C*(M*lambda.sqrt) := Nat.mul_le_mul_left _ hs
        _ = (C*lambda.sqrt)*M := by ring
    exact Nat.le_of_mul_le_mul_right hmul hM
  calc
    ((2:ℕ)^d)^6 = (8^d)^2 := by
      rw [← pow_mul, show (8:ℕ)=2^3 by decide, ← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ (C*lambda.sqrt)^2 := Nat.pow_le_pow_left h8 _
    _ = C^2*lambda.sqrt^2 := by rw [mul_pow]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.sqrt_le' _)

/-- A floor-faithful sufficient threshold for λ^(4/5)≤u_d, in the
equivalent exact natural-number form λ^4≤u_d^5. -/
theorem printed_u_four_fifths (s M C d : ℕ)
    (hC : 0 < C)
    (hsize : (2*epsDen)^30 * C^10 ≤ Nat.clog 2 s)
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (shrink : 8^d*M ≤ C*s) :
    (Nat.clog 2 s)^4 ≤ (stepU (Nat.clog 2 s) d)^5 := by
  let lambda := Nat.clog 2 s
  let w := epsDen*2^d
  let u := stepU lambda d
  have hp : 0 < (2*epsDen)^30*C^10 := by unfold epsDen; positivity
  have hl : 0 < lambda := hp.trans_le hsize
  have h6 := depth_sixth_bound s M C d hl active shrink
  have hw : 0 < w := by unfold w epsDen; positivity
  have h30 : (2*w)^30 ≤ lambda^6 := by
    calc
      (2*w)^30 = (2*epsDen)^30 * (((2:ℕ)^d)^6)^5 := by
        unfold w
        rw [← pow_mul, ← mul_assoc, mul_pow]
      _ ≤ (2*epsDen)^30 * (C^2*lambda)^5 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h6 _)
      _ = ((2*epsDen)^30 * C^10)*lambda^5 := by rw [mul_pow (C^2) lambda, ← pow_mul C]; ring
      _ ≤ lambda*lambda^5 := Nat.mul_le_mul_right _ hsize
      _ = lambda^6 := by rw [← pow_succ']
  have h5 : (2*w)^5 ≤ lambda := by
    apply (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : (6:ℕ) ≠ 0)).mp
    rw [← pow_mul]
    exact h30
  have hwp : (2*w)^1 ≤ (2*w)^5 :=
    Nat.pow_le_pow_right (show 0 < 2*w by omega) (by decide)
  rw [pow_one] at hwp
  have hw' : w ≤ (2*w)^5 := (show w ≤ 2*w by omega).trans hwp
  have hu : 1 ≤ u := by
    change 1 ≤ lambda/w
    exact (Nat.le_div_iff_mul_le hw).mpr (by simpa using hw'.trans h5)
  have hround : lambda ≤ (2*w)*u := by
    have hmod := Nat.mod_lt lambda hw
    have hsplit := Nat.mod_add_div lambda w
    have hwu : w ≤ w*u := by simpa using Nat.mul_le_mul_left w hu
    change lambda % w + w*u = lambda at hsplit
    rw [show 2*w*u = w*u+w*u by ring]
    omega
  have hpow := Nat.pow_le_pow_left hround 5
  rw [mul_pow] at hpow
  have hr : lambda^5 ≤ lambda*u^5 :=
    hpow.trans (Nat.mul_le_mul_right _ h5)
  have hexp : lambda^5=lambda*lambda^4 := by rw [← pow_succ']
  rw [hexp] at hr
  exact Nat.le_of_mul_le_mul_left hr hl

#print axioms stepA_bound
#print axioms stepA_has_u
#print axioms active_wire_lower
#print axioms depth_sixth_bound
#print axioms printed_u_four_fifths

end J1PPrinted

