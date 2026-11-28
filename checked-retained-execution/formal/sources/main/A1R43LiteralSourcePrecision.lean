import A1R43LiteralAdmission

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000

/-! Exact printed word precision on the literal A1 root at t=-1.
The height and root mesh width come from the active source schedule,
independently of the number of equalized class copies. -/
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

theorem exact_native_minus_one_precision (guard : PrintedMargins m) :
    registerPrecision S r (negativeCenter F W f guard) =
      (Fintype.card V+1) +
        8*height (floorWires m) (J9PrintedSchedule.rootU (Nat.clog 2 s))*lengthL m +
        8*floorWires m*(nativeA m+1) := by
  have he := root_wire_count F W f guard
  have ha : (S).levelBits (r).depth=nativeA m :=
    (root_bits F W f guard).trans guard.full_dim
  have hu : (S).levelWidth (r).depth=J9PrintedSchedule.rootU (Nat.clog 2 s) := rfl
  have h0 : (r).prec=Fintype.card V+1 := rfl
  have ht : (negativeCenter F W f guard).val=(-1:ℤ) := rfl
  unfold registerPrecision childPrecision
  rw [ht,ha,he,hu,h0]
  have hv : padicValInt 2 (-1:ℤ)=0 := by
    change padicValInt 2 (1:ℤ)=0
    exact padicValInt.one
  simp [J9PrintedSchedule.precision,lengthL,hv]

#print axioms exact_native_minus_one_precision
end
end A1R43Literal
