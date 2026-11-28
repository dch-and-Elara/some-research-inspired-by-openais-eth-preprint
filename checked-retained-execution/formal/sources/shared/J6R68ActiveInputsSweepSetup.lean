import J6R68ActiveInputsSweepCore
import J6R67UnifiedRateFee

/-! One real capture serves the base roster, high-margin word, every
R62 centre controller and the shared copy register. There is no
legacy active supplier in this program. -/
namespace J6R68ActiveInputs.Sweep
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 J6R22Active J6ActiveSchedule
open J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R49DFS J6R58ActivePrep
open J6R62ActivePrep J6R63Active J6R64Active J6R67UnifiedRate
open J6R17ModeTape J6R57ActiveFee J6R52FreshExterior

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18600000
set_option maxRecDepth 3800
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s q pw ew cw n : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f} {good : n ≤ 2^f.natDegree}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (Shape.levelBits (printedParams (f:=f) (ell:=ell) s) c.depth)
local notation "U" => (Shape.levelWidth (printedParams (f:=f) (ell:=ell) s) c.depth)

def prepare (hq : 0<q) (fit : InputFits sel d q) (taperPos : 0<U) (taperSmall : U ≤ c.edges)
    (hf : f.Monic) (chart : MaskTable f.natDegree n good) (cover : physicalProbeCount f ell s c ≤ n)
    (header : Meter (CallWords c pw ew)) (layout : Meter (AtLayout sel d cw)) :
    Meter (Schedule sel d bank q) :=
  let words := header.result
  let stock := prepareStockFromHeader (s:=s) hq words
  let receipt := actual_current_word_builds_stock_and_margin hq words fit taperPos taperSmall
  let copies := copyOfLayout q layout.result
  let law := (retained_layout_copy_word layout.result fit.copies).1
  ⟨⟨stock.result,receipt.1,receipt.2.1,fun x live =>
    centreFromStock receipt.1 x live rfl hf chart cover hq fit taperPos taperSmall
      words copies.result law⟩,header.steps+layout.steps+copies.steps+stock.steps+4⟩

theorem prepare_uses_captured_inputs_once (hq : 0<q)
    (fit : InputFits sel d q) (taperPos : 0<U) (taperSmall : U ≤ c.edges)
    (hf : f.Monic) (chart : MaskTable f.natDegree n good) (cover : physicalProbeCount f ell s c ≤ n)
    (header : Meter (CallWords c pw ew)) (layout : Meter (AtLayout sel d cw)) :
    let P := prepare (bank:=bank) hq fit taperPos taperSmall hf chart cover header layout
    let B := prepareStockFromHeader (s:=s) hq header.result
    P.result.stock=B.result ∧ P.result.extra=commonLoss A c.edges U ∧
      P.steps=header.steps+layout.steps+(2*cw+4*q+5)+B.steps+4 := by
  refine ⟨rfl,?_,?_⟩
  · exact (actual_current_word_builds_stock_and_margin hq header.result fit taperPos taperSmall).2.1
  · dsimp only [prepare]
    rw [(retained_layout_copy_word layout.result fit.copies).2]

def stockSetupRoof (a u q ew : ℕ) : ℕ :=
  (2*ew+4*q+5)+taperFee q u+(baseTapeRoof a u q+commonLossWordRoof a q+4)+6

theorem prepare_bill_has_no_legacy_charge (hq : 0<q)
    (fit : InputFits sel d q) (taperPos : 0<U) (taperSmall : U ≤ c.edges)
    (hf : f.Monic) (chart : MaskTable f.natDegree n good) (cover : physicalProbeCount f ell s c ≤ n)
    (header : Meter (CallWords c pw ew)) (layout : Meter (AtLayout sel d cw)) :
    (prepare (bank:=bank) hq fit taperPos taperSmall hf chart cover header layout).steps ≤ header.steps+layout.steps+(2*cw+4*q+5)+stockSetupRoof A U q ew+4 := by
  rw [(prepare_uses_captured_inputs_once (bank:=bank) hq fit taperPos taperSmall hf chart cover header layout).2.2]
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (actual_current_word_builds_stock_and_margin hq header.result fit taperPos taperSmall).2.2 _) 4

theorem prepare_at_emitted_row_keeps_true_paid_tape_and_probe (hq : 0<q)
    (fit : InputFits sel d q) (taperPos : 0<U) (taperSmall : U ≤ c.edges)
    (hf : f.Monic) (chart : MaskTable f.natDegree n good) (cover : physicalProbeCount f ell s c ≤ n)
    (header : Meter (CallWords c pw ew)) (layout : Meter (AtLayout sel d cw)) :
    let D := (prepare (bank:=bank) hq fit taperPos taperSmall hf chart cover header layout).result
    ∀ x : D.EmitRow,
      let t := D.tag x
      let C := copyOfLayout q layout.result
      let copyLaw := (retained_layout_copy_word layout.result fit.copies).1
      let native := paidTape hq (fit.axis t) (centreWords hq fit taperPos taperSmall header.result C.result copyLaw t)
      (D.fetch x).tape.result=native.result ∧
      (D.fetch x).tape.steps=native.steps+(10*(A+1)+5)*D.stock.rows.length+3+3 ∧
      (∀ z,((D.fetch x).masks z).result.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree _ d.fit z) ∧
        ((D.fetch x).masks z).steps=(z.val+1)*(3*f.natDegree+5)) := by
  dsimp only
  intro x
  let B := prepareStockFromHeader (s:=s) hq header.result
  have e := actual_current_word_builds_stock_and_margin hq header.result fit taperPos taperSmall
  let t := centreFor (c:=c) (s:=s) e.1 x.val x.property
  have equal := actual_centre_consumes_stock_with_old_R23_value (t:=t) (bank:=bank) e.1 x.val x.property
    rfl hf chart cover hq fit taperPos taperSmall header.result (copyOfLayout q layout.result).result
    (retained_layout_copy_word layout.result fit.copies).1 .num
  exact equal.2
end

#print axioms prepare
#print axioms prepare_uses_captured_inputs_once
#print axioms prepare_bill_has_no_legacy_charge
#print axioms prepare_at_emitted_row_keeps_true_paid_tape_and_probe
end J6R68ActiveInputs.Sweep
