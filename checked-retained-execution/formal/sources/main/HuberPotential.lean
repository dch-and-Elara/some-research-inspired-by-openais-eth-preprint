import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Pointwise inequalities for a bounded-slope convex potential. These give
the exact quadratic remainder in the central simultaneous-correlation proof. -/

namespace HuberPotential

def rho (x : ℚ) : ℚ :=
  if x ≤ -4 then -4 * x - 8 else if x ≤ 4 then x ^ 2 / 2 else 4 * x - 8

def slope (x : ℚ) : ℚ :=
  if x ≤ -4 then -4 else if x ≤ 4 then x else 4

theorem slope_bound (x : ℚ) : -4 ≤ slope x ∧ slope x ≤ 4 := by
  unfold slope
  split_ifs <;> constructor <;> linarith

theorem supporting_line (x y : ℚ) :
    rho x + slope x * (y - x) ≤ rho y := by
  unfold rho slope
  split_ifs <;>
    nlinarith [sq_nonneg (y - x), sq_nonneg (x + 4), sq_nonneg (x - 4),
      sq_nonneg (y + 4), sq_nonneg (y - 4)]

theorem rho_quadratic (x : ℚ) (hx1 : -4 ≤ x) (hx2 : x ≤ 4) :
    rho x = x ^ 2 / 2 := by
  unfold rho
  split_ifs <;> nlinarith

theorem slope_central (x : ℚ) (hx1 : -2 ≤ x) (hx2 : x ≤ 2) :
    slope x = x := by
  unfold slope
  split_ifs <;> linarith

theorem central_flip_identity (x h : ℚ)
    (hx1 : -2 ≤ x) (hx2 : x ≤ 2) (hh1 : -2 ≤ h) (hh2 : h ≤ 2) :
    rho (x - h) - rho x = -h * slope x + h ^ 2 / 2 := by
  rw [rho_quadratic (x - h) (by linarith) (by linarith),
    rho_quadratic x (by linarith) (by linarith), slope_central x hx1 hx2]
  ring

theorem flip_remainder (x h : ℚ) (hh1 : -2 ≤ h) (hh2 : h ≤ 2) :
    -h * slope x + (if -2 ≤ x ∧ x ≤ 2 then h ^ 2 / 2 else 0)
      ≤ rho (x - h) - rho x := by
  by_cases hx : -2 ≤ x ∧ x ≤ 2
  · rw [if_pos hx, central_flip_identity x h hx.1 hx.2 hh1 hh2]
  · rw [if_neg hx]
    have hs := supporting_line x (x - h)
    nlinarith

#print axioms slope_bound
#print axioms supporting_line
#print axioms rho_quadratic
#print axioms slope_central
#print axioms central_flip_identity
#print axioms flip_remainder

end HuberPotential
