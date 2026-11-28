import A1R43LiteralSourcePrecision
import A1R43LiteralPrecision

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5100000

/-! Close the polynomial word-width estimate on the concrete A1 root,
using its degree-three original graph to discharge the base-width guard. -/
namespace A1R43Literal
open scoped Polynomial
open Polynomial J1PPrinted J6ActiveRun J6ActiveSchedule J6R12Blueprint
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
variable (W : PairPlan F (smallA (Nat.card (Occ F))) (copies (Nat.card (Occ F))))
variable (f : ℤ[X])
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "r" => starRoot F W f

theorem actual_named_word_width_poly (guard : PrintedMargins m)
    (cubic : ∀ v,GraphCutMoments.degree F v=3) :
    registerPrecision S r (negativeCenter F W f guard)≤(s+1)+40*s^2 := by
  have hsize : m=3*Fintype.card V :=
    (simulated_incidence_count F).trans (GraphCutMoments.regular_edge_count F 3 cubic)
  have hbase : Fintype.card V+1≤s+1 := by
    unfold starSize
    omega
  have hb := printed_minus_one_width m (Fintype.card V+1) guard hbase
  have hv : padicValInt 2 (-1:ℤ)=0 := by
    change padicValInt 2 (1:ℤ)=0
    exact padicValInt.one
  unfold childPrecision at hb
  simp only [J9PrintedSchedule.precision,hv,pow_zero,Nat.div_one] at hb
  exact (exact_native_minus_one_precision F W f guard).le.trans hb

theorem actual_omitted_bank_probe_count_poly (guard : PrintedMargins m) :
    J9PrintedSchedule.probeCount (r).edges (2^((S).levelBits (r).depth))≤2*s^2+1 := by
  have hb := (source_packing_conditions s (half m) 0 guard.u_pos guard.active_half).2.1
  rw [source_D_zero,source_L_zero] at hb
  have hd : 1≤fullCells m := by
    unfold fullCells J9PrintedSchedule.arrayCard
    exact Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hL : lengthL m≤s := by
    have h := Nat.mul_le_mul_left (lengthL m) hd
    rw [mul_one] at h
    exact (h.trans hb).trans (guard.wire_window.1.trans guard.wire_window.2)
  have ha := (root_bits F W f guard).trans guard.full_dim
  rw [root_wire_count F W f guard,ha]
  change J9PrintedSchedule.probeCount (floorWires m) (lengthL m)≤2*s^2+1
  unfold J9PrintedSchedule.probeCount J9PrintedSchedule.degreeBound
  have hi : 2*lengthL m-1≤2*s :=
    (Nat.sub_le _ _).trans (Nat.mul_le_mul_left 2 hL)
  have ht := Nat.mul_le_mul guard.wire_window.2 hi
  have hpoly : s*(2*s)=2*s^2 := by ring
  rw [hpoly] at ht
  exact Nat.add_le_add_right ht 1

#print axioms actual_named_word_width_poly
#print axioms actual_omitted_bank_probe_count_poly
end
end A1R43Literal
