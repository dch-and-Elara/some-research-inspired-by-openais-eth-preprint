import J6R11Threshold

namespace J6R11Small
open J1PPrinted

def threshold (C : ℕ) : ℕ := (2*epsDen)^30*C^10

/-- Failure of the one explicit large-input guard falls in a genuine
finite size range depending only on the paper's fixed density constant. -/
theorem exception_size (s C : ℕ) (h : Nat.clog 2 s < threshold C) :
    s ≤ 2^(threshold C-1) := by
  have hh : Nat.clog 2 s ≤ threshold C-1 := by omega
  exact (Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))).mp hh

/-- Budget for enumerating every Boolean assignment on the finitely many
small sizes excluded from the asymptotic source construction. -/
theorem exception_assignments (s C M : ℕ) (h : Nat.clog 2 s < threshold C)
    (hM : M ≤ C*s) : (2:ℕ)^M ≤ 2^(C*2^(threshold C-1)) := by
  apply Nat.pow_le_pow_right (by decide)
  exact hM.trans (Nat.mul_le_mul_left C (exception_size s C h))

#print axioms exception_size
#print axioms exception_assignments
end J6R11Small
