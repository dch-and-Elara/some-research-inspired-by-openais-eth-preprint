import J6R108FinalDriverReady
import J6R75OuterTimeAdmit

/-! Build the selected group plan using a bank value actually returned
by the literal request. Its Ready field is derived from the two actual
issued meters. The same native R102 body, true source owner callback
and existing R68 selected layout are the ones installed in the plan. -/
namespace J6R108FinalDriver
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
open J6R64Active J6R66Active J6R66.BootPeak J6R57Public
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R57ScopeFee
open J6R75OuterTime J6R14ZeroMode J6R55Public J6R68AbsolutePrescribed
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 5500000
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
variable (prior : (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))) (r : Entry D.mark m native tc tj tw)
variable (sync : prior.synced) (reserve : ∀ a∈prior.headers,a.id.bits.take kp≠D.mark.bits)
variable (written : r∈S.requests.rows)
variable (Y : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw)
variable (source : Y=actualExterior (W:=W) D r)
variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel ((exteriorChild G ell Y.centre Y.sample Y.group)) Y.hf}
variable (choosePaid : (b : (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))) → ((submitResidentRow D S pad prior r)).result=some (b,true) → OwnsHeader Y.header.result b → Meter (OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate))
variable (F : RetainedAfter T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate cw)
variable (chart : Meter (MountedChart T))
variable (layout : ExteriorLayout (T:=T) (page:=pageKeyWidth m+pad) (cw:=cw) Y)
variable (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ)

def continueSelectedPublicGroup
    (b : (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))) (ack : ((submitResidentRow D S pad prior r)).result=some (b,true) ∧ OwnsHeader Y.header.result b) : Meter ((Block (T.frame ((Path.root : Path sel (exteriorChild G ell Y.centre Y.sample Y.group) (exteriorChild G ell Y.centre Y.sample Y.group)).reached)) ell)×(PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))) :=
  let selected := choosePaid b ack.1 ack.2
  let answer := runRawPhysicalExterior Y selected.result F chart.result layout retire b ack.2
  ⟨answer.result,selected.steps+chart.steps+answer.steps+3⟩

/-- Feed the chosen compiler the bank from the literal paid
acknowledgement. The equality to the expected bank is used only for
its indexed proof obligations. The actual selector's meter, e.g. an
actual chart/callback setup, is added before the original recursion. -/
def runAdmittedSelectedPublicGroup : Meter ((Block (T.frame ((Path.root : Path sel (exteriorChild G ell Y.centre Y.sample Y.group) (exteriorChild G ell Y.centre Y.sample Y.group)).reached)) ell)×(PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))) :=
  let safe := (accepted_entry_installs_that_actual_job D S pad prior r sync reserve written).1
  continueActualResult ((submitResidentRow D S pad prior r)) prior ((publishedBank D S pad prior r)) safe
    (fun b=>((submitResidentRow D S pad prior r)).result=some (b,true) ∧ OwnsHeader Y.header.result b)
    ⟨safe,(literal_exterior_owns_the_installed_head D S pad prior r Y source)⟩ (continueSelectedPublicGroup D S pad prior r Y choosePaid F chart layout retire)

theorem actual_admit_select_and_recurse_are_three_paid_parts :
    let safe := (accepted_entry_installs_that_actual_job D S pad prior r sync reserve written).1
    let picked := choosePaid ((publishedBank D S pad prior r)) safe ((literal_exterior_owns_the_installed_head D S pad prior r Y source))
    let raw := runRawPhysicalExterior Y picked.result F chart.result layout retire ((publishedBank D S pad prior r)) ((literal_exterior_owns_the_installed_head D S pad prior r Y source))
    runAdmittedSelectedPublicGroup D S pad prior r sync reserve written Y source choosePaid F chart layout retire=
       ⟨raw.result,((submitResidentRow D S pad prior r)).steps+(picked.steps+chart.steps+raw.steps+3)+4⟩ := by
  dsimp only [runAdmittedSelectedPublicGroup]
  exact continuation_reads_the_returned_meter_result ((submitResidentRow D S pad prior r)) prior ((publishedBank D S pad prior r))
    (accepted_entry_installs_that_actual_job D S pad prior r sync reserve written).1
    (fun b=>((submitResidentRow D S pad prior r)).result=some (b,true) ∧ OwnsHeader Y.header.result b)
    ⟨(accepted_entry_installs_that_actual_job D S pad prior r sync reserve written).1,(literal_exterior_owns_the_installed_head D S pad prior r Y source)⟩
    (continueSelectedPublicGroup D S pad prior r Y choosePaid F chart layout retire)

/-- This refers to the exact R75 kernel instantiated with the
machine and chart selected by this acknowledgement, not another
R92/R55 meter. Both newly executed input producers stay billed. -/
theorem run_with_paid_bank_choice_has_R75_kernel_and_keeps_its_setup_debits :
    let safe := (accepted_entry_installs_that_actual_job D S pad prior r sync reserve written).1
    let picked := choosePaid ((publishedBank D S pad prior r)) safe ((literal_exterior_owns_the_installed_head D S pad prior r Y source))
    let old := runAdmittedRaw D S pad prior r sync reserve written Y source picked.result F chart.result layout retire
    let actual := runAdmittedSelectedPublicGroup D S pad prior r sync reserve written Y source choosePaid F chart layout retire
    actual.result=old.result ∧ actual.steps=old.steps+picked.steps+chart.steps+3 := by
  dsimp only
  rw [actual_admit_select_and_recurse_are_three_paid_parts,
      publication_then_raw_is_one_actual_meter]
  refine ⟨rfl,?_⟩
  dsimp only
  omega

#print axioms run_with_paid_bank_choice_has_R75_kernel_and_keeps_its_setup_debits
#print axioms continueSelectedPublicGroup
#print axioms runAdmittedSelectedPublicGroup
#print axioms actual_admit_select_and_recurse_are_three_paid_parts
end
end J6R108FinalDriver

