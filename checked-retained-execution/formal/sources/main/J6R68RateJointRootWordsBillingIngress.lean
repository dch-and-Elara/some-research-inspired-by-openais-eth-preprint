import J6R68RateJointRootWordsOnlineBody
import J6R68RateJointRootWordsBilling
import J6R68RateJointRootWordsGeometry

/-! Assemble the actual first-occurrence fee from measured incoming
operations. At the stock joined boot the two structural identities
are joined_source_identity and joined_initial_body_and_mount_charged_once.
No correctness-only equality is allowed to transfer a runtime. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R34RootAtlas J6R50SourceProducer J6R24MeteredRecursion
open J6ActiveRun J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R48RawRoute J6R57ScopeFee J6R67UnifiedRate

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4200
set_option maxHeartbeats 8500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Here" => (Path.root : Path sel r r)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Slot" => ((Plan sel).Slot r)
local notation "TicketAt" => (fun w : Slot=>(Here).ticket w)
local notation "Machine" => (OnlineMachine T key prec tw bw page rate)

/-- Structural identities for the *same* root boot Meter, including
the actual additional owner acquisition and not a bound on it. -/
structure ActualFirstIngress (M : Machine) where
  exteriorKey : Word key
  build : ∀ w : Slot,Meter (FirstSlotBook T key prec tw bw page w)
  port : Slot→ℕ
  writer : ∀ w : Slot,Meter (PhysicalFile T (TicketAt w) (port w))
  ownerDebit : Slot→ℕ
  actualInput : ∀ w : Slot,(M.initial w).result.input=
    (replaceSelectedFirst (build w) exteriorKey (writer w)).result
  actualSteps : ∀ w : Slot,(M.initial w).steps=
    (replaceSelectedFirst (build w) exteriorKey (writer w)).steps+ownerDebit w

structure ActualIngressDimensions (M : Machine) (A : ActualFirstIngress M) where
  producer : ℕ
  keyWidth : ℕ
  rowCount : ℕ
  writerDebit : ℕ
  ownerDebit : ℕ
  wordWidth : ℕ
  roster : ℕ
  paid : ∀ w : Slot,(A.build w).steps ≤ producer ∧
    (A.build w).result.width ≤ keyWidth ∧ (A.build w).result.rows.length ≤ rowCount ∧
    (A.writer w).steps ≤ writerDebit ∧ A.ownerDebit w ≤ ownerDebit
  words : ∀ w : Slot,ActualFirstWidths (A.build w).result.datum wordWidth ∧
    (A.build w).result.datum.physical.result.raw.masks.length+
      (A.build w).result.datum.geometry.modes.length ≤ roster

def ingressBootBudget {M : Machine} {A : ActualFirstIngress M}
    (D : ActualIngressDimensions M A) : ℕ :=
  D.producer+(locateFee D.keyWidth D.rowCount+3*D.keyWidth+5)+3+D.writerDebit+4+D.ownerDebit

def ingressNativeBudget {M : Machine} {A : ActualFirstIngress M}
    (D : ActualIngressDimensions M A) : ℕ :=
  128*(D.wordWidth+1)*(1+D.wordWidth+r.edges+D.roster)

theorem actual_first_ingress_disjoint_root_lines
    {M : Machine} (A : ActualFirstIngress M) (D : ActualIngressDimensions M A)
    (pos : 0<key) (room : A.exteriorKey.val+1<2^key) (w : Slot) :
    (M.initial w).steps ≤ ingressBootBudget D ∧
    measuredWordProducers (sourceState M Here w).input ≤ ingressNativeBudget D ∧
    (M.initial w).result.birth.job.identifier=(increment A.exteriorKey).result := by
  let src := replaceSelectedFirst (A.build w) A.exteriorKey (A.writer w)
  obtain ⟨outer,id,issued⟩ := selected_first_replacement_bills_both_real_phases
    (A.build w) A.exteriorKey (A.writer w) pos room
  obtain ⟨setup,iw,ic,writer,owner⟩ := D.paid w
  obtain ⟨width,census⟩ := D.words w
  have look := locate_fee_mono_width_tables iw ic
  have native := exact_first_copy_tariff_bounded_by_true_widths (A.build w).result.datum D.wordWidth width
  constructor
  · rw [A.actualSteps w]
    apply (Nat.add_le_add_right outer _).trans
    unfold ingressBootBudget selectedFirstHandleFee
    omega
  · have transfer := (compiled_occurrence_priced_by_actual_producers_and_chart src.result).1.symm
    change measuredWordProducers (M.initial w).result.input ≤ _ ∧
      (compileOccurrence (M.initial w).result.input).job.identifier=_
    rw [A.actualInput w]
    refine ⟨(transfer.trans issued).le.trans (native.trans ?_),id⟩
    unfold ingressNativeBudget
    apply Nat.mul_le_mul_left
    change 1+D.wordWidth+r.edges+(A.build w).result.datum.physical.result.raw.masks.length+
      (A.build w).result.datum.geometry.modes.length ≤ _
    omega

def scopeWithMeasuredIngress {M : Machine} {B : L} (Q : RemainingScopeInputs M B)
    (A : ActualFirstIngress M) (D : ActualIngressDimensions M A)
    (pos : 0<key) (room : A.exteriorKey.val+1<2^key) : MeasuredScopeInputs M B :=
  scopeWithActualFirst Q (ingressBootBudget D) (ingressNativeBudget D)
    (fun w=>(actual_first_ingress_disjoint_root_lines A D pos room w).1)
    (fun w=>(actual_first_ingress_disjoint_root_lines A D pos room w).2.1)

#print axioms actual_first_ingress_disjoint_root_lines
#print axioms scopeWithMeasuredIngress
end
end J6R68RateJoint.RootWords

