import J6R36SharedGatewayTop
import J6R35GatewayPreparationSelected

/-! Specialize the shared chart and frame to the same deterministic
field search used by the original nonzero J6 reduction. The data
fields here are real remaining input port/timing/width guards, not a
caller-supplied claimed receiver-frame Meter. -/
namespace J6R36SharedGateway
open scoped Polynomial Classical BigOperators
open Polynomial Std.Sat AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost P11FullPacking J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R14ZeroMode
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R25StableCensus J6R26StablePreparedRoot J6R27PrescribedProbe J6R28GeneratedRootFrame J6R29BinaryFieldSearch
open J6R34OfficialGateway J6R35GatewayPreparation J6R33OriginalJ6
set_option maxHeartbeats 17500000
set_option maxRecDepth 2750
set_option linter.unusedSectionVars false

section Official
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {base ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "pm" => J6SourcePrecision.printed
local notation "plant" => physicalPlant (J7R10Readout.H F)

structure OfficialRootInputs (F : CNF V) (base ell q rr cc dd : ℕ) where
  lit : LiteralPortFile (physicalPlant (J7R10Readout.H F)) rr cc dd
  positive : 0<ell
  hq : 0<q
  qFits : 1<q
  copies : J6R15ModeCost.Word q
  receive : J6R15ModeCost.Word q
  copiesOK : copies.val=K (ms F)
  receiveOK : receive.val=pm (ms F) base
  copyFits : K (ms F)≤2^RootKey (ms F)
  code : ℕ
  codePos : 0<code
  codeOK : 1+(writeResidents (ms F) hq (oddAxis (ms F)) copies receive lit.raw).result.roster.modes.length<2^code

variable (O : PrintedRootGuard F base)
variable (I : OfficialRootInputs F base ell q rr cc dd)

noncomputable def OfficialRootInputs.usingSelected (X : FieldInput F base) :
    CommonInputs (T:=plant) (f:=X.f) (base:=base) ell q rr cc dd where
  field := X.frame
  hf := X.presentation.monic
  lit := I.lit
  positive := I.positive
  hq := I.hq
  qFits := I.qFits
  copies := I.copies
  receive := I.receive
  copiesOK := I.copiesOK
  receiveOK := I.receiveOK
  copyFits := I.copyFits
  code := I.code
  codePos := I.codePos
  codeOK := I.codeOK

noncomputable abbrev OfficialRootInputs.selectedCommon := I.usingSelected (generatedField O).result

noncomputable abbrev OfficialSharedRequests (pad edgew tc tj key prec tw bw : ℕ) :=
  SharedRequests (generatedField O).result.rootShape (I.selectedCommon O) pad edgew tc tj key prec tw bw

variable (pad : ℕ)
variable (supply : OfficialSharedRequests O I pad edgew tc tj key prec tw bw)

noncomputable def runOfficialShared : Meter (Word (printedAnswerWidth (ms F) base)) := by
  let search := generatedField O
  let X := search.result
  let common := I.usingSelected X
  letI : Fact (Irreducible (NativeProbeRing.residuePoly X.f)) := ⟨X.irreducible⟩
  let prep := CommonInputs.make (G:=X.rootShape) common
  let reply := paidUsingCache X.rootShape common pad supply prep.result rfl
  exact ⟨reply.result,(search.steps+prep.steps+4)+reply.steps+4⟩

theorem real_selected_count_and_bills :
    let X := (generatedField O).result
    letI : Fact (Irreducible (NativeProbeRing.residuePoly X.f)) := ⟨X.irreducible⟩
    let prep := selectedSharedRoot O I.lit ell I.hq I.copies I.receive
    let front := frontUsingCache X.rootShape (I.selectedCommon O) pad supply prep.result rfl
    let replies := actualReplyBill X.rootShape (I.selectedCommon O) pad supply prep.result rfl
    let e := printedFieldWidth (ms F) (literalNativeSize F)
    let s := physicalSize (ms F) (literalNativeSize F)
    let paid := runOfficialShared O I pad supply
    let pads := (exactPadOrder (ms F) (K (ms F)) (printedHalf (ms F)) (constantRootWord (ms F))).length
    bitsValue paid.result.val=PinnedCNF.modelCount F ∧
      paid.steps=prep.steps+front.steps+replies+4 ∧
      prep.steps≤(1024*9^2*2*2^6)*s^8+6+
        (frameBuildFee e (pm (ms F) base)+(positiveTapeFee e (literalDegree (ms F) (literalNativeSize F)+1)+3)+
          residentsFee (ms F) q 0 (pm (ms F) base) rr cc dd+storedHalfRowsFee (ms F)+6)+4 ∧
      front.steps+(buildRootBitBank X.rootShape ell).steps+4≤
        reductionFee (ms F) X.f.natDegree (literalNativeSize F) (printedRankWidth (ms F)) (printedHalf (ms F))
          (printedFactorWidth (ms F) (qs F)) (printedAnswerWidth (ms F) base) ell (pm (ms F) base)
          pads X.frame.result.hp := by
  let X := (generatedField O).result
  letI : Fact (Irreducible (NativeProbeRing.residuePoly X.f)) := ⟨X.irreducible⟩
  let prep := selectedSharedRoot O I.lit ell I.hq I.copies I.receive
  let C := I.selectedCommon O
  have exactOld := exact_source_count_and_separated_bill X.rootShape C pad supply X.initialPositive
  have preFee := (selected_shared_root_exact O I.lit ell I.hq I.qFits I.copies I.receive I.copiesOK I.receiveOK).2
  have D := operation_costs_reach_final_word X.rootShape C pad supply prep.result rfl
  refine ⟨exactOld.1,?_,preFee,exactOld.2.2⟩
  change prep.steps+(paidUsingCache X.rootShape C pad supply prep.result rfl).steps+4=
    prep.steps+(frontUsingCache X.rootShape C pad supply prep.result rfl).steps+
      actualReplyBill X.rootShape C pad supply prep.result rfl+4
  rw [D.fee]
  omega

end Official

#print axioms real_selected_count_and_bills
end J6R36SharedGateway