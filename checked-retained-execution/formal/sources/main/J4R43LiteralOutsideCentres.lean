import J4R43LiteralOutsideScalar
import J5R41LiteralChildCostSchedule

/-! Both signed extreme centres are actual printed active nodes
at the same schedule. No free existence assumption on a probe centre. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid P11FullPacking J6R10Repack J6ActiveRun J6R12Blueprint
open J6ActiveSchedule J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

def outerCentre (a : ℕ) (positive : Bool) : ℤ :=
  if positive then ((2^a:ℕ):ℤ)-1 else -((((2^a:ℕ):ℤ)-1))

theorem real_odd_extremes (a : ℕ) (ha : 0<a) (positive : Bool) :
    outerCentre a positive∈oddGrid a := by
  have hL : (0:ℕ)<2^a := by positivity
  have E : Even (2^a:ℕ) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    rw [pow_succ]
    exact ⟨2^j,by omega⟩
  obtain ⟨j,hj⟩ := E
  apply Finset.mem_filter.mpr
  have h : ((2^a:ℕ):ℤ)=(j:ℤ)+(j:ℤ) := by exact_mod_cast hj
  rcases positive with _|_
  · change -(((2^a:ℕ):ℤ)-1)∈grid a ∧ Odd (-(((2^a:ℕ):ℤ)-1))
    refine ⟨?_,⟨-(j:ℤ),by omega⟩⟩
    rw [mem_grid]
    simp only [pow₂,Nat.cast_pow,Nat.cast_ofNat] at *
    omega
  · change (((2^a:ℕ):ℤ)-1)∈grid a ∧ Odd (((2^a:ℕ):ℤ)-1)
    refine ⟨genuine_extreme_mem a,⟨(j:ℤ)-1,by omega⟩⟩

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0
local notation "u₀" => J6ActiveRun.Shape.levelWidth S 0
local notation "M₀" => Fintype.card (DWire F)

theorem root_level_width_eq_half : a₀=2*u₀ := by
  change stepA (Nat.clog 2 (oldRowSize F)) 0=2*stepU (Nat.clog 2 (oldRowSize F)) 0
  simp [stepA]

theorem printed_width_at_most_real_edges (d : ColumnReady F reg (f:=f)) : u₀≤M₀ := by
  have hA : u₀≤a₀ := d.widthFits
  have hp : 2^a₀*J9PrintedSchedule.arrayCard a₀≤M₀ := d.paddedSlots
  have pos : 0<J9PrintedSchedule.arrayCard a₀ := by
    unfold J9PrintedSchedule.arrayCard; positivity
  have e : a₀ ≤ (2:ℕ)^a₀ := by
    exact le_of_lt Nat.lt_two_pow_self
  exact hA.trans (e.trans ((Nat.le_mul_of_pos_right _ pos).trans hp))

def actualOuterCenter (d : ColumnReady F reg (f:=f))
    (ha : 0<a₀) (positive : Bool) : ColumnCenter F reg (f:=f) := by
  have hu : 0<u₀ := by
    have h := root_level_width_eq_half (f:=f) F
    omega
  exact ⟨outerCentre a₀ positive,
    oddGrid_subset_active a₀ M₀ u₀ hu (printed_width_at_most_real_edges F reg d)
      (real_odd_extremes a₀ ha positive)⟩

theorem actual_outer_nocasual_input (d : ColumnReady F reg (f:=f))
    (ha : 0<a₀) (positive : Bool) :
    let c := actualOuterCenter F reg d ha positive
    c.val=outerCentre a₀ positive ∧ padicValInt 2 c.val=0 := by
  dsimp only [actualOuterCenter]
  exact ⟨rfl,odd_valuation_zero (Finset.mem_filter.mp (real_odd_extremes a₀ ha positive)).2⟩

#print axioms real_odd_extremes
#print axioms root_level_width_eq_half
#print axioms printed_width_at_most_real_edges
#print axioms actualOuterCenter
#print axioms actual_outer_nocasual_input
end
end J4R43LiteralOutside

