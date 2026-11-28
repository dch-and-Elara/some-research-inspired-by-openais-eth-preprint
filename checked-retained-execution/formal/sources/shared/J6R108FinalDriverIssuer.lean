import J6R102NativeCodeMeterJoined
import J6R55PublicReady

/-! A selected least-mode-code runtime and its actual paid scanner
do not change the first or later issuers. Use only same-result facts
to prove ownership/readiness; the additional R102 fees are untouched. -/
namespace J6R108FinalDriver
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R54PublicFamily J6R57ScopeFee J6R88ScopeCode
open J6R55BootBodies J6R55TerminalOrigin J6R48GeneratedAddons
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R55TerminalBootJoined J6R53OldOwnerRoot J6R54TerminalBoot J6R54ExteriorOwner
open J6R92NativeWidth J6R102NativeCodeMeter J6R55Public J6R16ModeCost

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4900
set_option maxHeartbeats 19000000
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local instance sourceEq : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (Ext)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {own rate : ℕ} {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (A : FirstBodyProgram X gate pad T)
variable (D : OwnerWordsAtBodies X gate pad root A)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)
local notation "Measured" => (withMeteredNativeCode X gate pad A root M D B live rootInj)
local notation "Minimal" => (withMinimalNativeCode X gate pad root M A D B live rootInj)

theorem new_first_writer_keeps_the_original_full_issuer_meter
    (w : (Plan sel).Slot Ext) :
    ((Measured).initial w).result.input.issued=(A.old w).result.issued := by
  have current := (same_initial_result_and_one_additional_roster_scan X gate pad A root M D B live rootInj w).1
  change ((Measured).initial w).result=((Minimal).initial w).result at current
  rw [current]
  have first := joined_issued_meter_is_original X gate pad root (withMinimalDemand M)
    (minimalFirstProgram X gate pad A) (minimalFirstOwners X gate pad A root D) B live rootInj w
  exact first

theorem paid_demand_keeps_the_exact_source_issuer_on_this_current_site
    {v : Ticket sel Ext} (Y : StoredSite T v key prec tw bw Pg) (w : (Plan sel).Slot v.child) :
    ((Measured).demand Y w).result.event.issued=(M.demand Y w).result.event.issued := by
  have current := (same_demand_result_and_one_additional_roster_scan X gate pad A root M D B live rootInj Y w).1
  change ((Measured).demand Y w).result=((Minimal).demand Y w).result at current
  rw [current]
  rfl

theorem actual_paid_code_machine_uses_the_two_raw_issuers
    (first : ∀ w : (Plan sel).Slot Ext,(A.old w).result.issued=increment X.issue.result)
    (next : ∀ {v : Ticket sel Ext} (Y : StoredSite T v key prec tw bw Pg) (w : (Plan sel).Slot v.child),
      (M.demand Y w).result.event.issued=increment Y.birth.job.identifier) :
    UsesFirstIssuer (Measured) (increment X.issue.result) ∧ UsesChildIncrement (Measured) := by
  refine ⟨?_,?_⟩
  · intro w
    exact (new_first_writer_keeps_the_original_full_issuer_meter X gate pad root M A D B live rootInj w).trans
      (first w)
  · intro c p u w
    let Y := sourceState (Measured) p u
    exact (paid_demand_keeps_the_exact_source_issuer_on_this_current_site X gate pad root M A D B live rootInj Y w).trans
      (next Y w)

#print axioms new_first_writer_keeps_the_original_full_issuer_meter
#print axioms paid_demand_keeps_the_exact_source_issuer_on_this_current_site
#print axioms actual_paid_code_machine_uses_the_two_raw_issuers
end
end J6R108FinalDriver

