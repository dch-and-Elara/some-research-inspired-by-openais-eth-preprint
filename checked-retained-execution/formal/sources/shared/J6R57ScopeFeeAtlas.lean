import J6R34RootAtlasOccurrence

/-! Every actual compiled native occurrence bills its own primitive
word producers and its genuine page compiler. The latter is bounded
by the explicit R33 arithmetic tariff on this occurrence's resident
geometry, not by an assumed bound on a free PageJob.built callback. -/
namespace J6R57ScopeFee
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R34RootAtlas J6R33GeneratedChildSite
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

variable {v : Ticket sel r}

def measuredWordProducers (I : OccurrenceInput T v key prec tw bw page) : ℕ :=
  I.issued.steps+(I.native.steps+I.physical.steps+I.words.steps+4)

noncomputable def literalAtlasTariff (I : OccurrenceInput T v key prec tw bw page) : ℕ :=
  runFee (ell:=ell) (code:=I.code) (tw:=tw) (bw:=bw) (fw:=I.fw) I.geometry+3

theorem birth_width_cast_preserves_compiler_debits {a b : ℕ} (eq : a=b)
    (Q : Birth T v key prec tw bw a) :
    let next := (eq ▸ Q : Birth T v key prec tw bw b)
    next.issuance.steps=Q.issuance.steps ∧ next.compilePages.steps=Q.compilePages.steps := by
  cases eq
  exact ⟨rfl,rfl⟩

theorem compiled_occurrence_priced_by_actual_producers_and_chart
    (I : OccurrenceInput T v key prec tw bw page) :
    (compileOccurrence I).issuance.steps=measuredWordProducers I ∧
      (compileOccurrence I).compilePages.steps≤literalAtlasTariff I := by
  let cert := Classical.choice (occurrence_real_receipt I)
  let paid := padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  let Q := issuedBirth I.native.result paid I.words.result I.hOld cert
  have a := birth_width_cast_preserves_compiler_debits I.width Q
  change (compileOccurrence I).issuance.steps=Q.issuance.steps ∧
    (compileOccurrence I).compilePages.steps=Q.compilePages.steps at a
  refine ⟨a.1.trans rfl,?_⟩
  rw [a.2]
  exact cert.rowsFee

end
#print axioms measuredWordProducers
#print axioms literalAtlasTariff
#print axioms birth_width_cast_preserves_compiler_debits
#print axioms compiled_occurrence_priced_by_actual_producers_and_chart
end J6R57ScopeFee
