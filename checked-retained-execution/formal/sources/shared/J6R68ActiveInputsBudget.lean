import J6R68ActiveInputsLayout

/-! Uniform fee of the two actual finite loops. The dense key side is
absorbed using the printed padded-slot premise. The actual number of
vertex keys is explicit because isolated keys need not count as edges. -/
namespace J6R68ActiveInputs
open scoped Polynomial Classical
open AOracleMachineTime AOracleMachineTimeTape J6R10Repack P11FullPacking
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionMenu J6R12CollisionSource
open J6R12CollisionGraphScore J6R12CollisionGreedyStep J6R11CollisionReindex J6R14LayoutCost J6R17ModeTape
open V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000
set_option maxRecDepth 2650
set_option Elab.async false

def selectionScoreWidth (K : ℕ) : ℕ := 2*(K+6*K)+1

def selectorWriteRoof (K : ℕ) : ℕ := (writeBudget K K (6*K)+6)*K

def selectorStepRoof (K : ℕ) : ℕ :=
  (selectorWriteRoof K+scoreGraphBudget (selectionScoreWidth K) K K (6*K) K+
    8+12*selectionScoreWidth K+2*(6*K)+8)*K+selectorWriteRoof K+8

def labelRoof (K : ℕ) : ℕ :=
  (2*K+2*K+14)*K+
    ((selectorStepRoof K+2*(6*K)+6)*(K+K)+
      16*(6*K+1)*K+12*selectionScoreWidth K+20)

def selectedLayoutRoof (K : ℕ) : ℕ :=
  labelRoof K+fixedPoly K K (6*K) K K K+6

section Geometry
variable {E R C : Type*} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
variable {N : Network E R C} (I : Full64Input N a)

structure LayoutScales (q K : ℕ) : Prop where
  edgeWord : I.format.e≤K
  rowWord : I.format.kR≤K
  colWord : I.format.kC≤K
  queueWord : q≤K
  dimension : a≤K
  edgeCount : Fintype.card E≤K
  rowCount : Fintype.card R≤K
  colCount : Fintype.card C≤K

theorem same_layout_native_dimensions_bound_fee (q K : ℕ) (W : LayoutScales I q K)
    (slots : 2^a*J9PrintedSchedule.arrayCard a≤Fintype.card E) :
    I.fee+packFixedCap I.format.kR I.format.kC I.format.b q a (Fintype.card E)+6≤
      selectedLayoutRoof K := by
  have menu : 2^I.format.b*2^I.format.b≤Fintype.card E :=
    source_menu_fit a I.format.b _ I.labelWidth slots
  have side : 2^(6*a)≤K := by
    rw [←I.labelWidth]
    exact (alphabet_fit_menu _).trans (menu.trans W.edgeCount)
  have eb := W.edgeWord
  have rb := W.rowWord
  have cb := W.colWord
  have qb := W.queueWord
  have ab := W.dimension
  have ec := W.edgeCount
  have rc := W.rowCount
  have cc := W.colCount
  have bw : I.format.b≤6*K := I.labelWidth.symm ▸ Nat.mul_le_mul_left 6 ab
  have sw : I.format.width≤selectionScoreWidth K := by
    unfold Format.width scoreWidth selectionScoreWidth
    omega
  have selector : I.fee≤labelRoof K := by
    unfold Full64Input.fee labelRoof selectorStepRoof selectorWriteRoof selectionScoreWidth
      Format.width Format.stepBound Format.candidateBound Format.writeBound scoreWidth
      writeBudget scoreGraphBudget copyBudget pairBudget
    gcongr <;> exact sw
  have fixed : fixedPoly I.format.kR I.format.kC I.format.b q a (Fintype.card E)≤
      fixedPoly K K (6*K) K K K := by
    unfold fixedPoly menuPoly tagStepCap boxStepCap roundCap exportTapeCap headerCap seatStepCap
      scanStepCap recordTraffic seatTraffic
    gcongr
  exact Nat.add_le_add_right (Nat.add_le_add selector
    ((packFixedCap_poly _ _ _ _ _ _ menu).trans fixed)) 6

theorem paid_same_selection_layout_upper (P : PhysicalPacking N a (Fin 64))
    (q K : ℕ) (hq : 0<q) (ha : a≤q) (fit : Fintype.card E<2^q)
    (coord : ∀ w,I.format.label w=coordinateLabel w)
    (caught : I.run.result.1=I.format.graph (fun v=>some (wordsOf P v)))
    (rounded : RoundsExactly P) (measured : I.run.steps≤I.fee)
    (W : LayoutScales I q K) (slots : 2^a*J9PrintedSchedule.arrayCard a≤Fintype.card E) :
    (activeLayoutFromPaidLabels I P q hq ha fit coord caught rounded).steps≤selectedLayoutRoof K := by
  refine (fixed_export_of_same_paid_labels I P q hq ha fit coord caught rounded).2.2.2.2.2.trans ?_
  exact (Nat.add_le_add_right (Nat.add_le_add_right measured _) _).trans
    (same_layout_native_dimensions_bound_fee I q K W slots)
end Geometry

#print axioms same_layout_native_dimensions_bound_fee
#print axioms paid_same_selection_layout_upper
end J6R68ActiveInputs
