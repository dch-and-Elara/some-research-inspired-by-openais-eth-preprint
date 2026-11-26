
import S11TraceCore

namespace S11

theorem center_reached (M u L : ℕ) (hM : 0 < M) (hu : 0 < u) (t : ℤ) :
    t ∈ centers u L ↔ -(L:ℤ) ≤ t ∧ t < L ∧ t ≠ 0 ∧ 0 < multiplicity M u t := by
  have hh := three_mul_le_taper_mul (M := M) hu
  have hh' : 0 < taper M u := by
    by_contra! h
    have h0 : taper M u = 0 := by omega
    rw [h0,zero_mul] at hh
    omega
  have hpos : (0 < taper M u * (u - level t)) ↔ level t < u := by
    constructor
    · intro hp
      by_contra! hn
      rw [Nat.sub_eq_zero_of_le hn,mul_zero] at hp
      omega
    · intro hl
      exact Nat.mul_pos hh' (by omega)
  simp only [centers, Finset.mem_filter, Finset.mem_Ico, multiplicity, hpos, and_assoc]

def binaryProbe (e k : ℕ) (cap : k ≤ 2^e) (j : Fin k) : BitVec e :=
  BitVec.ofFin (j.castLE cap)

theorem binaryProbe_injective (e k : ℕ) (cap : k ≤ 2^e) :
    Function.Injective (binaryProbe e k cap) := by
  intro x y h
  have hn : (binaryProbe e k cap x).toNat = (binaryProbe e k cap y).toNat :=
    congrArg (fun w : BitVec e => w.toNat) h
  exact Fin.ext hn

theorem root_probe_capacity {M s : ℕ} (hM : M ≤ 3*s) (hu : 0 < retained s 0) :
    probeCount M (packetLength s 0) ≤ 2^(4*lambda s) := by
  let lam := lambda s
  have hLam : 131072 ≤ lam := by
    have h := (Nat.le_div_iff_mul_le (by decide : 0 < 131072 * 2^0)).1 hu
    simpa [lam] using h
  have hs : s ≤ 2^lam := (Nat.clog_le_iff_le_pow (by decide : 1<2)).1 le_rfl
  have ha : 2 * retained s 0 ≤ lam := by
    have h := Nat.div_mul_le_self lam (131072 * 2^0)
    change retained s 0 * (131072 * 2^0) ≤ lam at h
    simp only [pow_zero,mul_one] at h
    omega
  have hL : packetLength s 0 ≤ 2^lam := by
    rw [(root_parameters s).2]
    exact Nat.pow_le_pow_right (by decide) ha
  have hbound : M ≤ 3 * 2^lam := hM.trans (Nat.mul_le_mul_left _ hs)
  have hz : 0 < 2^lam := by positivity
  have hprod : M * (2 * packetLength s 0 - 1) ≤ (3 * 2^lam) * (2 * 2^lam) :=
    Nat.mul_le_mul hbound ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ hL))
  have he : (3 * 2^lam) * (2 * 2^lam) + 1 ≤ (2:ℕ)^(2*lam+3) := by
    have hsq : 0 < (2^lam) * (2^lam) := Nat.mul_pos hz hz
    have h1 : (3 * 2^lam) * (2 * 2^lam) = 6 * (2^lam * 2^lam) := by ring
    have h2 : (2:ℕ)^(2*lam+3) = 8 * (2^lam * 2^lam) := by
      rw [show 2*lam+3 = lam+lam+3 by omega, pow_add, pow_add]
      ring
    rw [h1,h2]
    omega
  exact (Nat.add_le_add_right hprod 1).trans (he.trans (Nat.pow_le_pow_right (by decide) (by omega)))

#print axioms center_reached
#print axioms binaryProbe_injective
#print axioms root_probe_capacity

end S11

