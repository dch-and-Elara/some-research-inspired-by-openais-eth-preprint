import J6R57LeafCapNumbers
import J6R18ChildWriteGeometric

/-! Independent numerical half of the generated packet-entry cost. The
exponential factor uses the actual printed mesh and can be absorbed in
a leaf exponent once the input roster fits a polynomial in s. The
remaining packet-local polynomial expressions are exposed. -/
namespace J6R57LeafCap
open J1PPrinted J6R16ModeCost J6R18ChildWrite
set_option autoImplicit false
set_option warningAsError true

theorem printed_axis_at_most_half (lambda d : ℕ) : 2*stepA lambda d≤lambda := by
  have hlo := (J9PrintedSchedule.rootU_range lambda).1
  have ha := stepA_bound lambda d
  omega

theorem half_mesh_times_log_le_leaf (s a : ℕ) (large : 1024≤Nat.clog 2 s)
    (small : 2*a≤Nat.clog 2 s) :
    (2:ℕ)^a*Nat.clog 2 s≤J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) := by
  let lam := Nat.clog 2 s
  let H := J9PrintedSchedule.leafThreshold s lam
  let u := lam-1-a
  change 1024≤lam at large
  change 2*a≤lam at small
  have hu : 32≤u := by unfold u; omega
  have huLam : lam≤3*u := by unfold u; omega
  have huSum : a+u=lam-1 := by unfold u; omega
  have hPos : 0<lam.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hPow : lam^2≤(2:ℕ)^u := by
    calc
      _≤(3*u)^2 := Nat.pow_le_pow_left huLam 2
      _=9*u^2 := by ring
      _≤16*u^5 := Nat.mul_le_mul (by decide)
        (Nat.pow_le_pow_right (by omega) (by decide))
      _≤_ := sixteen_pow5_le u hu
  have hs : (2:ℕ)^(lam-1)<s := (Nat.lt_clog_iff_pow_lt (b:=2) (by decide)).mp
    (by change lam-1<lam; omega)
  have hRound : s≤H*lam.sqrt := J9PrintedSchedule.le_roundup_mul s lam.sqrt hPos
  apply Nat.le_of_mul_le_mul_right _ hPos
  calc
    _≤(2:ℕ)^a*lam^2 := by
      rw [pow_two, mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sqrt_le_self _))
    _≤2^a*2^u := Nat.mul_le_mul_left _ hPow
    _=2^(lam-1) := by rw [← pow_add,huSum]
    _≤_ := hs.le.trans hRound

theorem actual_printed_packet_entry_geometric
    (s d E L p i q b r c m B : ℕ) (hp : 0<p) (large : 1024≤Nat.clog 2 s)
    (rowFit : r≤2^stepA (Nat.clog 2 s) d) (modeFit : m+2≤2^(B*Nat.clog 2 s)) :
    let a := stepA (Nat.clog 2 s) d
    let H := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
    packetFee a E L p i q b r c m hp+packetFramingFee E L p q≤
      2^(B*H)*(packetNonTreeFee a E L p i q b r c m hp+
        packetTreeScale E L p m r b q hp+packetFramingFee E L p q) := by
  let lam := Nat.clog 2 s
  let a := stepA lam d
  let H := J9PrintedSchedule.leafThreshold s lam
  have lift := half_mesh_times_log_le_leaf s a large (printed_axis_at_most_half lam d)
  have grow : (m+2)^(2^a)≤(2:ℕ)^(B*H) := by
    calc
      _≤(2^(B*lam))^(2^a) := Nat.pow_le_pow_left modeFit _
      _=2^(B*(2^a*lam)) := by rw [← pow_mul]; congr 1; ring
      _≤_ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left B lift)
  exact (packetFee_geometric a E L p i q b r c m hp rowFit).trans (Nat.mul_le_mul_right _ grow)

#print axioms printed_axis_at_most_half
#print axioms half_mesh_times_log_le_leaf
#print axioms actual_printed_packet_entry_geometric
end J6R57LeafCap
