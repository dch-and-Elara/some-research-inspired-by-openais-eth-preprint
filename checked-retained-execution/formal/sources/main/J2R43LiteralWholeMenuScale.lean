import J1PPrintedSize
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 1024

namespace J2R43LiteralWholeMenu
open J1PPrinted

def guardedQ (M L : ℕ) : ℕ := M/(4*L)

theorem one_error_le_eighth (M D L : ℕ) (hL : 0<L)
    (room : 320*D*L≤M) :
    Real.sqrt ((D:ℝ)*(5*(M:ℝ)/(L:ℝ)))≤(M:ℝ)/(8*(L:ℝ)) := by
  have h₁ : 0<(L:ℝ) := by exact_mod_cast hL
  have hM : (0:ℝ)≤M := by positivity
  have h₂ : (320:ℝ)*(D:ℝ)*(L:ℝ)≤(M:ℝ) := by exact_mod_cast room
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  rw [div_pow]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(8*(L:ℝ))^2)).mpr
  calc
    _ = (320*(D:ℝ)*(L:ℝ))*(M:ℝ) := by
      field_simp
      ring
    _ ≤ (M:ℝ)*(M:ℝ) := mul_le_mul_of_nonneg_right h₂ hM
    _ = _ := by ring

theorem two_errors_le_quarter (M D L : ℕ) (hD : 1≤D) (hL : 0<L)
    (room : 320*D*L≤M) :
    Real.sqrt (5*(M:ℝ)/(L:ℝ))+
      Real.sqrt ((D:ℝ)*(5*(M:ℝ)/(L:ℝ)))≤(M:ℝ)/(4*(L:ℝ)) := by
  have h := one_error_le_eighth M D L hL room
  have h₀ : Real.sqrt (5*(M:ℝ)/(L:ℝ))≤
      Real.sqrt ((D:ℝ)*(5*(M:ℝ)/(L:ℝ))) := by
    apply Real.sqrt_le_sqrt
    exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hD)
  have ht : (M:ℝ)/(4*(L:ℝ)) =
      (M:ℝ)/(8*(L:ℝ))+(M:ℝ)/(8*(L:ℝ)) := by
    have hl : (L:ℝ)≠0 := by exact_mod_cast hL.ne'
    field_simp
    ring
  rw [ht]
  exact add_le_add (h₀.trans h) h

theorem guardedQ_le (M L : ℕ) (hL : 0<L) :
    (guardedQ M L:ℝ)≤(M:ℝ)/(4*(L:ℝ)) := by
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4*(L:ℝ))).mpr
  exact_mod_cast (Nat.div_mul_le_self M (4*L))

theorem guardedQ_scale (M L : ℕ) (hL : 0<L) (hr : 4*L≤M) :
    M≤8*L*guardedQ M L := by
  have hp : 0<4*L := by positivity
  have hq : 1≤guardedQ M L :=
    (Nat.le_div_iff_mul_le hp).mpr (by simpa using hr)
  calc
    M = 4*L*guardedQ M L+M%(4*L) := (Nat.div_add_mod M (4*L)).symm
    _ ≤ 4*L*guardedQ M L+4*L := Nat.add_le_add_left (Nat.mod_lt _ hp).le _
    _ ≤ 4*L*guardedQ M L+4*L*guardedQ M L := by
      exact Nat.add_le_add_left (by simpa only [mul_one] using Nat.mul_le_mul_left (4*L) hq) _
    _ = _ := by ring

theorem guardedQ_from_two_errors (M D L K : ℕ) (hD : 1≤D) (hL : 0<L)
    (room : 320*D*L≤M)
    (hK : (M:ℝ)/(2*(L:ℝ))≤(K:ℝ)+Real.sqrt (5*(M:ℝ)/(L:ℝ))+
      Real.sqrt ((D:ℝ)*(5*(M:ℝ)/(L:ℝ)))) : guardedQ M L≤K := by
  have hε := two_errors_le_quarter M D L hD hL room
  have hl : (L:ℝ)≠0 := by exact_mod_cast hL.ne'
  have he : (M:ℝ)/(2*(L:ℝ)) =
      (M:ℝ)/(4*(L:ℝ))+(M:ℝ)/(4*(L:ℝ)) := by
    field_simp
    ring
  rw [he] at hK
  have hx := guardedQ_le M L hL
  exact_mod_cast (show (guardedQ M L:ℝ)≤(K:ℝ) by linarith only [hε,hK,hx])

/-- A simple finite threshold using the printed bounds, uniformly for any
actual depth; we use it at the literal old-row root. -/
theorem printed_guard_small (s d M : ℕ) (hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 s))
    (size : 320^2≤s) (mass : s≤M) :
    320*stepD (Nat.clog 2 s) d*stepL (Nat.clog 2 s) d≤M := by
  let A := stepD (Nat.clog 2 s) d
  let B := stepL (Nat.clog 2 s) d
  have h := dimensions_small s d hU
  have hA : A^4≤s :=
    (Nat.pow_le_pow_right (by unfold A stepD J9PrintedSchedule.arrayCard; positivity) (by decide : 4≤1000)).trans h.2.le
  have hB : B^4≤s :=
    (Nat.pow_le_pow_right (by unfold B stepL; positivity) (by decide : 4≤1000)).trans h.1.le
  have hAB : ((A*B)^2)^2≤s^2 := by
    calc
      _ = A^4*B^4 := by ring
      _ ≤ _ := by simpa [pow_two] using Nat.mul_le_mul hA hB
  have hSq : (A*B)^2≤s := (Nat.pow_le_pow_iff_left (by decide : (2:ℕ)≠0)).mp hAB
  change 320*A*B≤M
  rw [mul_assoc]
  apply le_trans _ mass
  by_cases ht : A*B≤320
  · simpa only [pow_two] using (Nat.mul_le_mul_left 320 ht).trans size
  · have hm := Nat.mul_le_mul_right (A*B) (Nat.le_of_lt (Nat.lt_of_not_ge ht))
    exact hm.trans_eq ((pow_two (A*B)).symm) |>.trans hSq

#print axioms one_error_le_eighth
#print axioms two_errors_le_quarter
#print axioms guardedQ_le
#print axioms guardedQ_scale
#print axioms guardedQ_from_two_errors
#print axioms printed_guard_small
end J2R43LiteralWholeMenu