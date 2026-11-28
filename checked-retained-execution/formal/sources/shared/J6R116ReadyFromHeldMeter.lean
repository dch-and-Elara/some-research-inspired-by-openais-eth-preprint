import J6R116ReadyFromHeld

/-! Bill the actual R114 operand assembly once, then the remaining
retained inputs on its same physical receipt. This starts after the
admission: the caller already owns its returned descriptor and bank. -/
namespace J6R116ReadyFromHeld
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R62ActivePrep J6R64Active J6R66Active J6R66.BootPeak J6R57Public
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R57ScopeFee
open J6R108FinalDriver J6R111KeptOwnerFlow J6R114SelectedOperands
open J6R68RateJoint.RootWords

open J6R75OuterTime J6R14ZeroMode J6R55Public
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 3800000
set_option pp.maxSteps 1100
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {rate : ℕ}
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W D i j g).hf}

local instance heldReadyMeterDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) ((exteriorChild G ell i j g))) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)



variable (rootInj : Function.Injective rootName)
variable (sync : prior.synced)
variable (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)



variable (R : PublicOperandReceipt (W:=W) D pad i j g gate root T rate)

variable (A : ResidentAdmissionCarry (W:=W) D pad)
variable (sameSite : R.observed=A.site) (sameBank : R.bank=A.receipt.1)
variable (extras : Meter (RemainingRetainedInputs D pad i j g gate root rootInj R))

/-- This variant consumes a held, already charged operand receipt. -/
def prepareReadyFromAnAlreadyHeldReceipt : Meter (ReadyRetainedPayload A) :=
  ⟨readyFromActualHeldOperands D pad i j g gate root rootInj R A sameSite sameBank extras.result,
    extras.steps+4⟩

variable (readFrom :
  ∀ (B : ResidentAdmissionCarry (W:=W) D pad)
    (same : B.site=literalSite W D i j g)
    (b : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)),
    OwnsHeader B.site.header.result b →
    Meter (RawSelectedSources pad gate root B.site
      (preparedAtOtherSource B.site (literalSite W D i j g) same T) rate))

variable (returned : (submitResidentRowKeepingSite D S pad prior (sourceRow (W:=W) D i j g)).result=some A)
variable (checkRemaining :
  (Z : PublicOperandReceipt (W:=W) D pad i j g gate root T rate) →
    Meter (RemainingRetainedInputs D pad i j g gate root rootInj Z))

/-- The preparer of the retained group, for a source whose admission
was executed by its real caller. This does not admit the row or emit
an exterior descriptor. Its two input producer costs remain visible. -/
def prepareReadyFromTheActualReturnedAdmission : Meter (ReadyRetainedPayload A) :=
  let O := operandsFromOneRetainedAdmission D S pad prior i j g gate root rootInj
    sync reserved readFrom A returned
  let both := held_admission_passes_the_identical_site_and_bank D S pad prior i j g gate root rootInj
    sync reserved readFrom A returned
  let extra := checkRemaining O.result
  let ready := prepareReadyFromAnAlreadyHeldReceipt D pad i j g gate root rootInj
    O.result A both.1 both.2.1 extra
  ⟨ready.result,O.steps+ready.steps⟩

theorem the_actual_preparer_returns_source_scale :
    let actual := prepareReadyFromTheActualReturnedAdmission D S pad prior i j g gate root rootInj
      sync reserved A readFrom returned checkRemaining
    actual.result.size=physicalSize m native ∧ actual.result.constant=2 ∧
      HEq actual.result.selector (G.selector ell) := by
  dsimp only [prepareReadyFromTheActualReturnedAdmission,prepareReadyFromAnAlreadyHeldReceipt]
  exact actual_held_retained_payload_has_source_scale D pad i j g gate root rootInj _ _ _ _ _

theorem the_actual_preparer_charges_exactly_the_two_actual_operands :
    let O := operandsFromOneRetainedAdmission D S pad prior i j g gate root rootInj
      sync reserved readFrom A returned
    (prepareReadyFromTheActualReturnedAdmission D S pad prior i j g gate root rootInj
      sync reserved A readFrom returned checkRemaining).steps =
      O.steps+((checkRemaining O.result).steps+4) := rfl

theorem the_actual_preparer_uses_the_paid_code_and_first_spool :
    let O := operandsFromOneRetainedAdmission D S pad prior i j g gate root rootInj
      sync reserved readFrom A returned
    let ready := prepareReadyFromTheActualReturnedAdmission D S pad prior i j g gate root rootInj
      sync reserved A readFrom returned checkRemaining
    HEq ready.result.machine (machineOnHeldOperandsWithRealCode D pad i j g gate root rootInj O.result) ∧
    HEq ready.result.first (firstOwnerSourceOnTheSameHeldOperands D pad i j g gate root rootInj O.result) := by
  dsimp only [prepareReadyFromTheActualReturnedAdmission,prepareReadyFromAnAlreadyHeldReceipt]
  exact ready_on_the_held_bank_keeps_the_exact_R102_machine_and_first D pad i j g gate root rootInj _ _ _ _ _

#print axioms prepareReadyFromAnAlreadyHeldReceipt
#print axioms prepareReadyFromTheActualReturnedAdmission
#print axioms the_actual_preparer_returns_source_scale
#print axioms the_actual_preparer_charges_exactly_the_two_actual_operands
#print axioms the_actual_preparer_uses_the_paid_code_and_first_spool
end
end J6R116ReadyFromHeld

