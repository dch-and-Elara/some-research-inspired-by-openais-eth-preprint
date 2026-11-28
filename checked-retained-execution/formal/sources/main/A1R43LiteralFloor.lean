import A1R43LiteralSchedule

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000

/-! Exact rounding loss for the A1 source slots. In particular the
printed M/s -> 1 does not require an extra admissibility hypothesis. -/
namespace A1R43Literal

theorem floor_slack_exact (m : ℕ) :
    starSize m-floorWires m=starSize m%(fullCells m*lengthL m) := by
  have hs := Nat.mod_add_div (starSize m) (fullCells m*lengthL m)
  change starSize m%(fullCells m*lengthL m)+(fullCells m*lengthL m)*copies m=starSize m at hs
  have h : (fullCells m*lengthL m)*copies m=floorWires m := by unfold floorWires; ring
  rw [h] at hs
  omega

theorem root_cell_span (m : ℕ) :
    fullCells m*lengthL m=2^(13*nativeA m) := by
  unfold fullCells lengthL
  rw [J9PrintedSchedule.arrayCard_power]
  calc
    _ = ((2:ℕ)^nativeA m)^13 := (pow_succ ((2:ℕ)^nativeA m) 12).symm
    _ = _ := by rw [← pow_mul,mul_comm (nativeA m) 13]

theorem rounding_slack_square_lt (m : ℕ) (guard : PrintedMargins m) :
    (starSize m-floorWires m)^2<starSize m := by
  let l := Nat.clog 2 (starSize m)
  let u := J9PrintedSchedule.rootU l
  have hU : 1≤u := guard.u_pos
  have hu : 131072*u≤l := (J9PrintedSchedule.rootU_range l).1
  have hpos : 0<l := by omega
  have hexp : (13*nativeA m)*2≤l-1 := by
    change (13*(2*u))*2≤l-1
    omega
  have hspan : (fullCells m*lengthL m)^2≤(2:ℕ)^(l-1) := by
    rw [root_cell_span,← pow_mul]
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hexp
  have hclog : (2:ℕ)^(l-1)<starSize m :=
    (Nat.lt_clog_iff_pow_lt (by decide)).1 (by change l-1<l; omega)
  have hr : starSize m-floorWires m<fullCells m*lengthL m := by
    rw [floor_slack_exact,root_cell_span]
    exact Nat.mod_lt _ (pow_pos (by decide) _)
  exact ((Nat.pow_le_pow_left hr.le 2).trans hspan).trans_lt hclog

#print axioms floor_slack_exact
#print axioms root_cell_span
#print axioms rounding_slack_square_lt
end A1R43Literal
