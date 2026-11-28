import J6R114SelectedOperandsAck
import J6R111KeptOwnerFlowSharedAdmissionExact

/-! Consume the physical site and bank from the same paid R111 admission.
Canonical-address alignment is proof data, not another descriptor read
or installation. -/
namespace J6R114SelectedOperands
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
open J6R108FinalDriver J6R111KeptOwnerFlow
open J6R68RateJoint.RootWords

open J6R75OuterTime J6R14ZeroMode J6R55Public
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 8500000
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

local instance readOperandsDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) ((exteriorChild G ell i j g))) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)



variable (rootInj : Function.Injective rootName)
variable (sync : prior.synced)
variable (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)

include sync reserved in
/-- The paid admission result itself identifies the exact physical
exterior and acknowledged bank at the prescribed triple. -/
theorem checked_physical_admission_indices
    (A : ResidentAdmissionCarry (W:=W) D pad)
    (returned : (submitResidentRowKeepingSite D S pad prior (sourceRow (W:=W) D i j g)).result=some A) :
    A.site=literalSite W D i j g ∧
    (submitResidentRow D S pad prior (sourceRow (W:=W) D i j g)).result=some (A.receipt.1,true) := by
  obtain ⟨R,hit,_,site,accepted,_,_⟩ :=
    actual_canonical_admission_keeps_the_exact_site_from_that_head
      D S pad prior i j g (prepareHead W i j).result rfl sync reserved
  have e : A=R := Option.some.inj (returned.symm.trans hit)
  subst A
  exact ⟨site,accepted⟩

variable (readFrom :
  ∀ (A : ResidentAdmissionCarry (W:=W) D pad)
    (h : A.site=literalSite W D i j g)
    (b : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)),
    OwnsHeader A.site.header.result b →
    Meter (RawSelectedSources pad gate root A.site
      (preparedAtOtherSource A.site (literalSite W D i j g) h T) rate))

/-- No admission fee is added here because the actual admission
result is supplied. Callers that run admission here use the billed
composite below. -/
def operandsFromOneRetainedAdmission
    (A : ResidentAdmissionCarry (W:=W) D pad)
    (returned : (submitResidentRowKeepingSite D S pad prior (sourceRow (W:=W) D i j g)).result=some A) :
    Meter (PublicOperandReceipt (W:=W) D pad i j g gate root T rate) :=
  let e := checked_physical_admission_indices D S pad prior i j g sync reserved A returned
  assembleAfterActualAck D S pad prior i j g gate root rootInj sync reserved A.site e.1
    (readFrom A e.1) A.receipt.1 e.2

theorem held_admission_passes_the_identical_site_and_bank
    (A : ResidentAdmissionCarry (W:=W) D pad)
    (returned : (submitResidentRowKeepingSite D S pad prior (sourceRow (W:=W) D i j g)).result=some A) :
    let output := operandsFromOneRetainedAdmission D S pad prior i j g gate root rootInj sync reserved readFrom A returned
    output.result.observed=A.site ∧ output.result.bank=A.receipt.1 ∧
    let e := checked_physical_admission_indices D S pad prior i j g sync reserved A returned
    output.result.sourceImports=readFrom A e.1 A.receipt.1 output.result.own :=
  ⟨rfl,rfl,rfl⟩

/-- One actual admission, and one assembly consuming the returned
physical values. There is no further entrySource read or root install. -/
def admitOnceAndBuildSelectedOperands :
    Meter (Option (PublicOperandReceipt (W:=W) D pad i j g gate root T rate)) :=
  let posted := submitResidentRowKeepingSite D S pad prior (sourceRow (W:=W) D i j g)
  match observed : posted.result with
  | none => ⟨none,posted.steps+4⟩
  | some A =>
    let M := operandsFromOneRetainedAdmission D S pad prior i j g gate root rootInj sync reserved readFrom A observed
    ⟨some M.result,posted.steps+M.steps+4⟩

theorem accounts_for_this_exact_successful_admit_and_build
    (A : ResidentAdmissionCarry (W:=W) D pad)
    (returned : (submitResidentRowKeepingSite D S pad prior (sourceRow (W:=W) D i j g)).result=some A) :
    let posted := submitResidentRowKeepingSite D S pad prior (sourceRow (W:=W) D i j g)
    let M := operandsFromOneRetainedAdmission D S pad prior i j g gate root rootInj sync reserved readFrom A returned
    admitOnceAndBuildSelectedOperands D S pad prior i j g gate root rootInj sync reserved readFrom =
      ⟨some M.result,posted.steps+M.steps+4⟩ := by
  dsimp only [admitOnceAndBuildSelectedOperands]
  split
  · rename_i impossible
    rw [returned] at impossible
    contradiction
  · rename_i R actual
    have e : R=A := Option.some.inj (actual.symm.trans returned)
    subst R
    rfl

#print axioms checked_physical_admission_indices
#print axioms operandsFromOneRetainedAdmission
#print axioms held_admission_passes_the_identical_site_and_bank
#print axioms admitOnceAndBuildSelectedOperands
#print axioms accounts_for_this_exact_successful_admit_and_build
end
end J6R114SelectedOperands

