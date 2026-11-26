import J6Mesh
import Mathlib.Tactic

/-! Exact finite centering margin at the J6 mesh. The address bound is
not substituted for the native precision. We use the source lower
bound on precision and an explicit cleared-integer height. -/
namespace J6Precision
open J6Mesh

def height (m t : ℕ) : ℕ := M m*(3+t*(a m+1))

theorem precision_gap (m t p : ℕ) (ht : t ≤ 2*m+1)
    (hSource : 24*M m*L m ≤ u m*p) :
    height m t + 1 < p := by
  let n := m+2
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hb0 := b_pos m
  have hb : b m ≤ n :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < (2:ℕ))).mpr
      (Nat.lt_pow_self (by decide : 1 < (2:ℕ))).le
  have hu0 : 0 < u m := by unfold u; omega
  have hu : u m ≤ 4*n := by unfold u; omega
  have h1 : t ≤ 2*n := by dsimp [n]; omega
  have h2 : a m+1 ≤ 9*n := by unfold a; omega
  have hh : t*(a m+1) ≤ (2*n)*(9*n) := Nat.mul_le_mul h1 h2
  have hv : 3+t*(a m+1) ≤ 20*n^2 := by nlinarith
  have hm0 : 0 < M m := by unfold M; positivity
  have hN : 2 ≤ M m*n^2 := by
    calc
      2 ≤ n^2 := by nlinarith
      _ ≤ M m*n^2 := Nat.le_mul_of_pos_left _ hm0
  have hg : height m t+2 ≤ 22*M m*n^2 := by
    have h := Nat.mul_le_mul_left (M m) hv
    unfold height
    nlinarith
  have hPow : 4*n^3 ≤ n^8 := by
    have h5 : 4 ≤ n^5 := by
      calc
        4 ≤ (2:ℕ)^5 := by decide
        _ ≤ _ := Nat.pow_le_pow_left hn _
    calc
      _ ≤ n^5*n^3 := Nat.mul_le_mul_right _ h5
      _ = _ := by rw [← pow_add]
  have hL : 4*n^3 ≤ L m := hPow.trans (size_powers m).1
  have hB : u m*(height m t+2) ≤ 24*M m*L m := by
    calc
      _ ≤ (4*n)*(22*M m*n^2) := Nat.mul_le_mul hu hg
      _ = 88*M m*n^3 := by ring
      _ ≤ 96*M m*n^3 := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (M m) (by decide))
      _ = (24*M m)*(4*n^3) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hL
  have hi : height m t+2 ≤ p := by
    by_contra! hbad
    exact (not_lt_of_ge (hB.trans hSource)) (Nat.mul_lt_mul_of_pos_left hbad hu0)
  omega

theorem centered_fit (m t p : ℕ) (ht : t ≤ 2*m+1)
    (hSource : 24*M m*L m ≤ u m*p) (num : ℤ)
    (hAbs : |num| ≤ (↑((2:ℕ)^height m t):ℤ)) :
    2*|num| < (↑((2:ℕ)^p):ℤ) := by
  have hp := precision_gap m t p ht hSource
  calc
    _ ≤ 2*(↑((2:ℕ)^height m t):ℤ) := mul_le_mul_of_nonneg_left hAbs (by decide)
    _ = (↑((2:ℕ)^(height m t+1)):ℤ) := by rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat,mul_comm]
    _ < _ := by exact_mod_cast (Nat.pow_lt_pow_right (by decide : (1:ℕ)<2) hp)

#print axioms precision_gap
#print axioms centered_fit
end J6Precision
