import J9PrintedSchedule

/-! Exact A4 padding parameters for an explicitly listed compact graph.
The exponent is read from the original planted wire count. Every tested
parameter below is finite and executable (no eventual-size hypothesis
is used except entering the positive-u active range where stated). -/

namespace ACompactLayout

def plantedWires (m o : ℕ) : ℕ := 6*(m+o)
def plantedSize (m o t : ℕ) : ℕ := 4*(m+o)+t+2*o
def rounds (w : ℕ) : ℕ := Nat.clog 2 (w+2)
def lambda (w : ℕ) : ℕ := 2*rounds w
def total (w : ℕ) : ℕ := 2^lambda w
def exponent (w : ℕ) : ℕ := J9PrintedSchedule.rootA (lambda w)
def packetLength (w : ℕ) : ℕ := 2^exponent w
def cells (w : ℕ) : ℕ := J9PrintedSchedule.arrayCard (exponent w)
def perCell (w : ℕ) : ℕ := 2^(lambda w-12*exponent w)
def packetCopies (w : ℕ) : ℕ := 2^(lambda w-13*exponent w)
def paddedSize (w delta : ℕ) : ℕ := total w-delta

theorem planted_delta (m o t : ℕ) (hd : 2*t+3*o=2*m) :
    plantedSize m o t ≤ plantedWires m o ∧
    plantedWires m o-plantedSize m o t=t+3*o := by
  unfold plantedWires plantedSize
  omega

theorem rounds_pos (w : ℕ) : 0 < rounds w :=
  Nat.clog_pos (by decide) (by omega)

theorem half_root_exponent (w : ℕ) : 13*exponent w ≤ rounds w := by
  have h := (J9PrintedSchedule.rootU_range (lambda w)).1
  change 131072 * J9PrintedSchedule.rootU (lambda w) ≤ 2*rounds w at h
  unfold exponent J9PrintedSchedule.rootA
  omega

theorem total_quadratic (w : ℕ) : total w ≤ 4*(w+2)^2 := by
  let q := rounds w
  have h0 : 0 < q := rounds_pos w
  have h := Nat.pow_pred_clog_lt_self (b:=2) (by decide) (x:=w+2) (by omega)
  change 2^(q-1) < w+2 at h
  have hq : 2^q ≤ 2*(w+2) := by
    rw [show q = (q-1)+1 by omega, pow_succ]
    omega
  change 2^(2*q) ≤ _
  rw [Nat.mul_comm 2 q,pow_mul]
  exact (Nat.pow_le_pow_left hq 2).trans (by ring_nf; omega)

theorem common_load (w : ℕ) :
    cells w * perCell w = total w ∧ perCell w = packetCopies w * packetLength w ∧
    w+2 ≤ perCell w := by
  have h := half_root_exponent w
  have h12 : 12*exponent w ≤ lambda w := by unfold lambda; omega
  have h13 : 13*exponent w ≤ lambda w := by unfold lambda; omega
  refine ⟨?_,?_,?_⟩
  · unfold cells perCell total
    rw [J9PrintedSchedule.arrayCard_power, ← pow_mul, Nat.mul_comm (exponent w) 12,
      ← pow_add, Nat.add_sub_of_le h12]
  · unfold perCell packetCopies packetLength
    rw [← pow_add]
    congr 1
    omega
  · have hround : rounds w ≤ lambda w-12*exponent w := by unfold lambda; omega
    exact (Nat.le_pow_clog (by decide) (w+2)).trans
      (Nat.pow_le_pow_right (by decide) hround)

theorem packetLength_even (w : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU (lambda w)) :
    Even (packetLength w) := by
  have hp : 0 < exponent w := by unfold exponent J9PrintedSchedule.rootA; omega
  refine ⟨2^(exponent w-1),?_⟩
  unfold packetLength
  rw [show exponent w = (exponent w-1)+1 by omega, pow_succ]
  have hf : (exponent w-1+1)-1=exponent w-1 := by omega
  rw [hf]
  omega

theorem padded_lambda (w delta : ℕ) (hd : delta ≤ w) :
    Nat.clog 2 (paddedSize w delta)=lambda w := by
  have hpos : 0 < lambda w := by
    have hh := rounds_pos w
    unfold lambda
    omega
  have hr : rounds w ≤ lambda w-1 := by
    have hh := rounds_pos w
    unfold lambda
    omega
  have small : w+2 ≤ 2^(lambda w-1) :=
    (Nat.le_pow_clog (by decide) (w+2)).trans (Nat.pow_le_pow_right (by decide) hr)
  have H : 2^lambda w = 2^(lambda w-1)*2 := by
    conv_lhs => rw [show lambda w=(lambda w-1)+1 by omega,pow_succ]
  apply le_antisymm
  · exact (Nat.clog_le_iff_le_pow (by decide)).2 (Nat.sub_le _ _)
  · have h : 2^(lambda w-1) < paddedSize w delta := by
      unfold paddedSize total
      rw [H]
      omega
    have h' := (Nat.lt_clog_iff_pow_lt (by decide)).2 h
    omega

theorem padded_active (w delta : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU (lambda w)) :
    J9PrintedSchedule.leafThreshold (paddedSize w delta) (lambda w) < total w := by
  have hp : 131072 ≤ lambda w := by
    have h := (J9PrintedSchedule.rootU_range (lambda w)).1
    omega
  have sq : 2 ≤ (lambda w).sqrt := Nat.le_sqrt.mpr (by omega)
  have hA : 2 ≤ total w := by
    change (2:ℕ)^1 ≤ 2^lambda w
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 1 ≤ lambda w)
  have hsize : paddedSize w delta ≤ total w := Nat.sub_le _ _
  unfold J9PrintedSchedule.leafThreshold
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < (lambda w).sqrt)).2
  have he := Nat.mul_le_mul (show 1 ≤ total w-1 by omega)
    (show 1 ≤ (lambda w).sqrt-1 by omega)
  have he1 : (total w-1)+1 = total w := by omega
  have he2 : ((lambda w).sqrt-1)+1 = (lambda w).sqrt := by omega
  have hexpand : total w * (lambda w).sqrt =
      (total w - 1) * ((lambda w).sqrt - 1) + (total w - 1) + ((lambda w).sqrt - 1) + 1 := by
    calc
      _ = ((total w-1)+1)*(((lambda w).sqrt-1)+1) := by rw [he1,he2]
      _ = _ := by ring
  omega

theorem word_exponent_linear (w : ℕ) : lambda w ≤ 2*(w+1) := by
  unfold lambda rounds
  exact Nat.mul_le_mul_left 2 ((Nat.clog_le_iff_le_pow (by decide)).2
    (J9PrintedSchedule.next_le_two_power (w+1)))

def layoutPayload (w : ℕ) : ℕ := 1+total w*(3*lambda w+8)

theorem layoutPayload_poly (w : ℕ) :
    layoutPayload w ≤ 57*(w+2)^3 := by
  have h := total_quadratic w
  have hl := word_exponent_linear w
  have he : 3*lambda w+8 ≤ 14*(w+2) := by omega
  have hn := Nat.mul_le_mul h he
  unfold layoutPayload
  nlinarith

#print axioms planted_delta
#print axioms total_quadratic
#print axioms common_load
#print axioms packetLength_even
#print axioms padded_lambda
#print axioms padded_active
#print axioms layoutPayload_poly

end ACompactLayout
