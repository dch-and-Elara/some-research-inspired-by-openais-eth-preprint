import J2R43LiteralWholeMenuScale

/-! The fixed additive reservation loss can be paid within the actual P9
depth q=floor(M/(4L)), without changing the root receiving precision. -/
namespace J2R47P9ZeroProbe
open J1PPrinted J2R43LiteralWholeMenu
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option maxRecDepth 2000
set_option exponentiation.threshold 1024
set_option linter.unusedSectionVars false

theorem reserved_guardedQ (M D L K : ℕ) (hD : 1≤D) (hL : 0<L)
    (room : 1280*D*L≤M)
    (bound : (M:ℝ)/(2*(L:ℝ))≤(K:ℝ)+
      Real.sqrt (5*(M:ℝ)/(L:ℝ))+
      Real.sqrt ((D:ℝ)*(5*(M:ℝ)/(L:ℝ)))+6) :
    guardedQ M L≤K := by
  have hDr : (1:ℝ)≤D := by exact_mod_cast hD
  have hLr : (0:ℝ)<L := by exact_mod_cast hL
  have hscale : 320*(4*D)*L≤M := by
    convert room using 1
    ring
  have hbig := one_error_le_eighth M (4*D) L hL hscale
  have same : ((4*D:ℕ):ℝ)*(5*(M:ℝ)/(L:ℝ)) =
      4*((D:ℝ)*(5*(M:ℝ)/(L:ℝ))) := by push_cast; ring
  rw [same,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
    show Real.sqrt (4:ℝ)=2 by norm_num] at hbig
  have small := Real.sqrt_le_sqrt
    (le_mul_of_one_le_left (by positivity : 0≤5*(M:ℝ)/(L:ℝ)) hDr)
  have limit : (6:ℝ)≤(M:ℝ)/(8*(L:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h0 : 48*L≤M := by
      calc
        _ ≤ (1280*D)*L := Nat.mul_le_mul_right _ (by omega)
        _ ≤ M := room
    have hc : (48:ℝ)*(L:ℝ)≤M := by exact_mod_cast h0
    linarith only [hc]
  have equ : (M:ℝ)/(2*(L:ℝ)) =
      (M:ℝ)/(4*(L:ℝ))+(M:ℝ)/(8*(L:ℝ))+(M:ℝ)/(8*(L:ℝ)) := by
    field_simp
    ring
  rw [equ] at bound
  have hq := guardedQ_le M L hL
  exact_mod_cast (show (guardedQ M L:ℝ)≤K by linarith only [hbig,small,limit,bound,hq])

theorem printed_reserved_room (s d M : ℕ) (hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 s))
    (size : 1280^2≤s) (mass : s≤M) :
    1280*stepD (Nat.clog 2 s) d*stepL (Nat.clog 2 s) d≤M := by
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
  change 1280*A*B≤M
  rw [mul_assoc]
  apply le_trans _ mass
  by_cases ht : A*B≤1280
  · simpa only [pow_two] using (Nat.mul_le_mul_left 1280 ht).trans size
  · have hm := Nat.mul_le_mul_right (A*B) (Nat.le_of_lt (Nat.lt_of_not_ge ht))
    exact hm.trans_eq ((pow_two (A*B)).symm) |>.trans hSq

#print axioms reserved_guardedQ
#print axioms printed_reserved_room
end J2R47P9ZeroProbe

