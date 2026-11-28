import J6R64ActiveMachine
import J6R22ActiveScaled

/-! No new overflow premise is needed at an active printed call.
The already checked register for the original odd centre covers the
stock multiplicities and common high-precision margin. -/
namespace J6R68ActiveInputs
open scoped Polynomial
open Polynomial P1DyadicGrid AOracleMachineTime J6ActiveSchedule J6R22Active HermiteLoss
open J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R63Active J6R64Active

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2700
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s q : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (Shape.levelBits (printedParams (f:=f) (ell:=ell) s) c.depth)
local notation "U" => (Shape.levelWidth (printedParams (f:=f) (ell:=ell) s) c.depth)

theorem true_native_registers_fit_base_operations
    (F : InputFits sel d q) (taperPos : 0<U) (taperSmall : U ≤ c.edges) :
    3*c.edges+U-1<2^q ∧ 4*c.edges<2^q ∧ commonLoss A c.edges U<2^q ∧
      c.edges<2^q ∧ U<2^q := by
  let a := A
  let u := U
  have inOdd : (-1:ℤ)∈oddGrid a := by
    refine Finset.mem_filter.mpr ⟨?_,by decide⟩
    rw [mem_grid]
    have h := pow₂_pos a
    omega
  let t : Center S c := ⟨-1,oddGrid_subset_active a c.edges u taperPos taperSmall inOdd⟩
  have iz : (centerIndex d t).val=0 := by
    change padicValInt 2 (-1)=0
    exact odd_valuation_zero (by decide)
  have pfit := F.register t
  rw [←printed_precision_at_same_centre d t,iz] at pfit
  have standard : c.prec+8*height c.edges u*2^a+8*c.edges*(a+1)<2^q := by
    simpa only [precisionAt,J9PrintedSchedule.precision,Nat.sub_zero,Nat.add_assoc,mul_assoc] using pfit
  have e : 4*c.edges ≤ (8*c.edges)*(a+1) :=
    (Nat.mul_le_mul_right c.edges (by decide : (4:ℕ) ≤ 8)).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have margin : commonLoss a c.edges u ≤ (8*height c.edges u)*2^a+(8*c.edges)*(a+1) := by
    unfold commonLoss
    change (6*height c.edges u)*2^a+(4*c.edges)*(a+1) ≤ _
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))) 
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))
  change u ≤ c.edges at taperSmall
  change 3*c.edges+u-1<2^q ∧ 4*c.edges<2^q ∧ commonLoss a c.edges u<2^q ∧
    c.edges<2^q ∧ u<2^q
  omega

#print axioms true_native_registers_fit_base_operations
end
end J6R68ActiveInputs
