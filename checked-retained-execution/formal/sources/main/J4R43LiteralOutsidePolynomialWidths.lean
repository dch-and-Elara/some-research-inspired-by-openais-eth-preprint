import J4R43LiteralOutsideUnitStrip
import J4R43LiteralOutsideCentres

/-! Native arithmetic budgets have polynomial-size widths from the
printed physical source itself. There is no extra bounded mesh
size assumption hidden in the fixed-band evaluator. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid J6ActiveRun J6R12Blueprint J6ActiveSchedule
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4400000

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0
local notation "M" => Fintype.card (DWire F)
local notation "s" => oldRowSize F

include reg in
theorem literal_edges_linear_in_old_size :
    M≤6*s := by
  rw [d_physical_wire_count F reg,oldRowSize]
  have e : Fintype.card (Clone W)=4*Fintype.card W := by
    rw [Fintype.card_prod,Fintype.card_fin,mul_comm]
  rw [e]
  omega

theorem literal_grid_and_width_polynomial (d : ColumnReady F reg (f:=f)) :
    2^a₀≤6*s ∧ 2*2^a₀-1≤12*s ∧ derivativeWidth a₀≤(6*s+1)*(12*s) := by
  have pos : 0<J9PrintedSchedule.arrayCard a₀ := by
    unfold J9PrintedSchedule.arrayCard
    positivity
  have L : 2^a₀≤6*s :=
    ((Nat.le_mul_of_pos_right _ pos).trans d.paddedSlots).trans (literal_edges_linear_in_old_size F reg)
  have A : a₀≤6*s := (Nat.lt_two_pow_self (n:=a₀)).le.trans L
  have n : 2*2^a₀-1≤12*s := by omega
  refine ⟨L,n,?_⟩
  unfold derivativeWidth
  exact Nat.mul_le_mul (Nat.succ_le_succ A) n

#print axioms literal_edges_linear_in_old_size
#print axioms literal_grid_and_width_polynomial
end
end J4R43LiteralOutside

