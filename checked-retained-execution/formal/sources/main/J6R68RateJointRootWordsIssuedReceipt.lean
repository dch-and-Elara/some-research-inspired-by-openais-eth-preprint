import J6R68RateJointRootWordsBody
import J6R50SourceProducerOnline

/-! Transfer the actual first-body fee to the stored immutable job.
The given input equality is the exact R55 assembler identity, not a
hypothesis on output, value correctness or producer fees. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R26DescriptorTree J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R55BootBodies J6R58BootScope J6R57ScopeFee J6R30ProducedGateRegistry J6R50SourceProducer
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4200
set_option maxHeartbeats 6600000
set_option Elab.async false
noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "RootSlot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "TicketAt" => (fun w : RootSlot=>(Path.root : Path sel Ext Ext).ticket w)
variable (K : ResidentFirstTemplates X pad T) (L : BootLaneTape X gate pad)
local notation "A" => (firstBodiesFromCheckedRootWords X gate pad K L)

theorem real_first_body_fee_is_exact_stored_issuance
    (w : RootSlot) (out : StoredSite T (TicketAt w) key prec tw bw Pg)
    (same : out.input=(bodyAtActualSlot X gate pad A w).result)
    (keyPositive : 0<key) (keyRoom : X.issue.result.val+1<2^key) :
    out.birth.job.identifier=(increment X.issue.result).result ∧
      out.birth.issuance.steps=firstReplayTariff (K.template w) (13*key+4)+4 ∧
      out.birth.job.identifier.val=X.issue.result.val+1 := by
  let F := bodyAtActualSlot X gate pad A w
  have H := actual_first_body_word_price_not_double_charged X gate pad K L keyPositive keyRoom w
  change (compileOccurrence out.input).job.identifier=_ ∧
    (compileOccurrence out.input).issuance.steps=_ ∧ (compileOccurrence out.input).job.identifier.val=_
  rw [same]
  have printedKey : (compileOccurrence F.result).job.identifier=(increment X.issue.result).result :=
    (occurrence_identity F.result).1.trans (congrArg (fun i : Meter (Word key)=>i.result) H.1)
  have printedFee := (compiled_occurrence_priced_by_actual_producers_and_chart F.result).1.trans H.2.1
  exact ⟨printedKey,printedFee,(congrArg Word.val printedKey).trans
    (increment_exact keyPositive X.issue.result keyRoom).1⟩

#print axioms real_first_body_fee_is_exact_stored_issuance
end
end J6R68RateJoint.RootWords

