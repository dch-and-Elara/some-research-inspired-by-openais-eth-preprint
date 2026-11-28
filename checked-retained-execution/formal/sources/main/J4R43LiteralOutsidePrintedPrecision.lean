import J4R43LiteralOutsideCentres
import J4R43LiteralOutsideScalar

/-! The precise lower receiving precision invoked at the actual odd
extremes. This is the original printed p_t, not an enlarged receiver. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial J6ActiveRun J6R12Blueprint J6ActiveSchedule P1DyadicGrid
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4100000

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0
local notation "u₀" => J6ActiveRun.Shape.levelWidth S 0
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "M" => Fintype.card (DWire F)

theorem odd_source_precision_matches_print (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (odd : padicValInt 2 t.val=0) :
    24*M*2^a₀≤registerPrecision S root t*u₀ := by
  have H₀ := active_order_pos a₀ M u₀ t.val t.property
  unfold order at H₀
  rw [odd,Nat.sub_zero] at H₀
  have hu : 0<u₀ := Nat.pos_of_ne_zero (by intro z; rw [z,mul_zero] at H₀; omega)
  have H := height_bounds M u₀ hu (printed_width_at_most_real_edges F reg d)
  have h : 8*(height M u₀)*2^a₀≤registerPrecision S root t := by
    change 8*(height M u₀)*2^a₀≤
      J9PrintedSchedule.precision (4*Fintype.card W+1) (height M u₀)
        ((2:ℕ)^a₀/2^padicValInt 2 t.val) M a₀
    rw [odd,pow_zero,Nat.div_one]
    unfold J9PrintedSchedule.precision
    omega
  calc
    _= (3*M)*(8*2^a₀) := by ring
    _≤ (height M u₀*u₀)*(8*2^a₀) := Nat.mul_le_mul_right _ H.1
    _= (8*height M u₀*2^a₀)*u₀ := by ring
    _≤_ := Nat.mul_le_mul_right _ h

theorem both_extreme_precision (d : ColumnReady F reg (f:=f))
    (ha : 0<a₀) (sign : Bool) :
    let t := actualOuterCenter F reg d ha sign
    24*M*2^a₀≤registerPrecision S root t*u₀ :=
  odd_source_precision_matches_print F reg d _ (actual_outer_nocasual_input F reg d ha sign).2

#print axioms odd_source_precision_matches_print
#print axioms both_extreme_precision
end
end J4R43LiteralOutside

