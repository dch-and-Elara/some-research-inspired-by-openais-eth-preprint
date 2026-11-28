import A1R43LiteralSchedule
import J6ActiveSchedule

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6700000

/-! A1's actual high register is still of polynomially bounded
precision. This is a bound on the printed bit width, not the cost of
acquiring the named value. -/
namespace A1R43Literal
open J1PPrinted J6ActiveSchedule

theorem printed_minus_one_width (m p0 : ℕ) (guard : PrintedMargins m)
    (base : p0≤starSize m+1) :
    childPrecision p0 (nativeA m) (floorWires m)
      (J9PrintedSchedule.rootU (Nat.clog 2 (starSize m))) (-1) ≤
      (starSize m+1)+40*(starSize m)^2 := by
  let s := starSize m
  let M := floorWires m
  let u := J9PrintedSchedule.rootU (Nat.clog 2 s)
  let a := nativeA m
  let L := lengthL m
  have hU : 0<u := guard.u_pos
  have huA : u≤a+1 := by
    change u≤2*u+1
    omega
  have hAL : a+1≤L := J9PrintedSchedule.next_le_two_power _
  have hLM : L≤M := by
    have h := (source_packing_conditions (starSize m) (half m) 0 guard.u_pos guard.active_half).2.1
    rw [source_D_zero,source_L_zero] at h
    have hd : 1≤fullCells m := by unfold fullCells J9PrintedSchedule.arrayCard; exact Nat.succ_le_of_lt (pow_pos (by decide) _)
    have h' : lengthL m*1 ≤ lengthL m*fullCells m := Nat.mul_le_mul_left _ hd
    rw [mul_one] at h'
    exact (h'.trans h).trans guard.wire_window.1
  have hUM : u≤M := huA.trans (hAL.trans hLM)
  have hM : M≤s := guard.wire_window.2
  have hL : L≤s := hLM.trans hM
  have hH : height M u≤4*s := by
    have h := (height_bounds M u hU hUM).2
    have hh := Nat.mul_le_mul_left (height M u) guard.u_pos
    rw [mul_one] at hh
    exact (hh.trans h).trans (Nat.mul_le_mul_left _ hM)
  change childPrecision p0 a M u (-1) ≤ _
  unfold childPrecision J9PrintedSchedule.precision
  have hh : padicValInt 2 (-1)=0 := by simp
  rw [hh,pow_zero,Nat.div_one]
  change p0+8*height M u*L+8*M*(a+1)≤(s+1)+40*s^2
  have p : 8*height M u*L≤8*(4*s)*s :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hH) hL
  have q : 8*M*(a+1)≤8*s*s :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) (hAL.trans hL)
  have h := Nat.add_le_add (Nat.add_le_add base p) q
  exact h.trans_eq (by ring)

#print axioms printed_minus_one_width
end A1R43Literal
