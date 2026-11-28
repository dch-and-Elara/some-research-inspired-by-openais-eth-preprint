import J1PhysicalParameters
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! The original source's integer rounding for Q and r gives precisely
the dyadic packing premise; no real/logarithmic exponent is assumed. -/
namespace J1PhysicalPrinted
def sourceNu (L : ℕ) := Nat.clog 2 L
def sourceR (L : ℕ) := Nat.sqrt L / (sourceNu L)^2
def sourceQ (L : ℕ) := L / (128*sourceNu L)

theorem sourceR_sq (L : ℕ) : (sourceR L)^2 ≤ L :=
  (Nat.pow_le_pow_left (Nat.div_le_self _ _) _).trans (Nat.sqrt_le' _)

theorem sourceQ_le (L : ℕ) : sourceQ L ≤ L := Nat.div_le_self _ _

/-- Exact version of D = r^(2Q) ≤ 2^(λ/128). -/
theorem source_packing (L : ℕ) : ((sourceR L)^(sourceQ L))^256 ≤ 2^L := by
  have hr : (sourceR L)^2 ≤ 2^sourceNu L :=
    (sourceR_sq L).trans (Nat.le_pow_clog (by decide) _)
  calc
    _ = ((sourceR L)^2)^(sourceQ L*128) := by
      rw [← pow_mul,← pow_mul]
      congr 1
      ring
    _ ≤ (2^sourceNu L)^(sourceQ L*128) := Nat.pow_le_pow_left hr _
    _ = 2^(sourceQ L*(128*sourceNu L)) := by rw [← pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self _ _)

/-- Original Q and r immediately discharge all three numeric guards once
the source alphabet is nonempty and the ceiling-log threshold is reached. -/
theorem source_guards (N : ℕ) (hN : 0 < N)
    (hL : 256 ≤ Nat.clog 2 (4*N))
    (hr : 0 < sourceR (Nat.clog 2 (4*N))) :
    let r := sourceR (Nat.clog 2 (4*N))
    let Q := sourceQ (Nat.clog 2 (4*N))
    192*Q*r^2*r^Q+6 < N ∧
      10*(r^(2*Q))^2 ≤ 12*N ∧ 2*Q*r^2 ≤ 4*N :=
  J1PhysicalParameters.ceiling_guards _ _ _ hN hL
    (sourceQ_le _) (sourceR_sq _) hr (source_packing _)

#print axioms source_packing
#print axioms source_guards
end J1PhysicalPrinted
