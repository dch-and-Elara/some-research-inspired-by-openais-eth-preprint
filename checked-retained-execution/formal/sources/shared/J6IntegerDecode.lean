import J6IntegerLayers
import J6IntegerRoot
import Mathlib.Data.ZMod.ValMinAbs

/-! This translates a centered residue of a uniformly denominator-cleared
slot into an exact integer signed root. It charges the root comparisons,
not the still separate bit-cost of each large intermediate exponentiation. -/
namespace J6IntegerDecode

def integerDecode (p e N : ℕ) (d u : ℤ) (z : ZMod (2^p)) : ℤ × ℕ :=
  J6IntegerRoot.signed p e ((((d : ZMod (2^p))^N * z).valMinAbs) / u)

theorem residue_root (p e N : ℕ) (d u a : ℤ) (z : ZMod (2^p))
    (hu : u ≠ 0) (he : Odd e)
    (hz : (d : ZMod (2^p))^N * z = ((u*a^e : ℤ) : ZMod (2^p)))
    (hf : 2*|u*a^e| < (↑((2:ℕ)^p) : ℤ)) :
    integerDecode p e N d u z = (a,p) := by
  letI : NeZero ((2:ℕ)^p) := ⟨pow_ne_zero _ (by decide)⟩
  have lifted : ((d : ZMod (2^p))^N*z).valMinAbs = u*a^e := by
    apply (ZMod.valMinAbs_spec _ _).mpr
    refine ⟨hz,?_⟩
    change -(↑((2:ℕ)^p):ℤ) < (u*a^e)*2 ∧ (u*a^e)*2 ≤ ↑((2:ℕ)^p)
    constructor <;> linarith [le_abs_self (u*a^e),neg_le_abs (u*a^e)]
  have he0 : 0 < e := by obtain ⟨j,hj⟩ := he; omega
  have habs : (u*a^e).natAbs < 2^p := by
    have bound : |u*a^e| < (↑((2:ℕ)^p) : ℤ) := by
      have hnon := abs_nonneg (u*a^e)
      omega
    exact_mod_cast (show ((u*a^e).natAbs : ℤ) < (↑((2:ℕ)^p) : ℤ) by simpa using bound)
  have un : 0 < u.natAbs := Int.natAbs_pos.mpr hu
  have leA : a.natAbs ≤ a.natAbs^e := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he0)
    by_cases h0 : a.natAbs = 0
    · simp [h0]
    · rw [pow_succ, Nat.mul_comm]
      exact Nat.le_mul_of_pos_right _ (pow_pos (Nat.pos_of_ne_zero h0) _)
  have hcap : a.natAbs < 2^p := by
    rw [Int.natAbs_mul,Int.natAbs_pow] at habs
    exact (leA.trans (Nat.le_mul_of_pos_left _ un)).trans_lt habs
  have div_exact : (u*a^e) / u = a^e := by
    rw [mul_comm,Int.mul_ediv_cancel _ hu]
  unfold integerDecode
  rw [lifted,div_exact]
  exact Prod.ext (J6IntegerRoot.signed_exact _ _ _ he hcap) (J6IntegerRoot.signed_steps _ _ _)

#print axioms residue_root
end J6IntegerDecode