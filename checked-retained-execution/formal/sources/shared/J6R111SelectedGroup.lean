import J6R108FinalDriverHandoff
import J6R75OuterTimeSlot
import J6R53WordIngressCharge

/-! A group receipt from the actual acknowledgement and its measured
setup. Equality to the registered plan is used only as a proof index.
The input providers execute on the returned bank, not in a shadow run. -/
namespace J6R111SelectedGroup
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath J6R35GatewayPreparation
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R19Retained AOracleMachineTimeTape A1R10 A1R12
open J6R34OfficialGateway J6R33OriginalJ6 J6R68AbsolutePrescribed J6R14ZeroMode
open J6R75OuterTime J6R108FinalDriver J6R64Active J6R66.BootPeak

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 21000000
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

local notation "Centre" => (J6Recovery.Addr m)
local notation "Sample" => (Fin (literalDegree m native+1))

variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (prior : (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)))
variable (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
variable (r : Entry D.mark m native tc tj tw) (written : r∈S.requests.rows)
variable (A : RawGroupPlan D S pad prior r cfg rate cw)
local notation "CurrentExterior" => (actualExterior (W:=W) D r)

structure PaidSetupForPlan where
  paidChosen : (b : (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))) → (submitResidentRow D S pad prior r).result=some (b,true) →
    OwnsHeader (actualExterior (W:=W) D r).header.result b →
    Meter (OnlineMachine A.prep (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
  paidChart : Meter (MountedChart A.prep)
  chosenExact : ∀ b ack own,(paidChosen b ack own).result=A.machine
  chartExact : paidChart.result=A.chart

variable (Q : PaidSetupForPlan D S pad prior r A)

def actualPaidOnWrittenRow : Meter (Block (frameOfPlan D S pad prior r A) ell) :=
  let physical := entrySource (W:=W) D r
  let run := runAdmittedSelectedPublicGroup D S pad prior r sync reserved written
    physical.result rfl Q.paidChosen A.keep Q.paidChart A.layout A.retire
  ⟨run.result.1,physical.steps+run.steps+3⟩

def actualSelectedSetupFee : ℕ :=
  let ack := (accepted_entry_installs_that_actual_job D S pad prior r sync reserved written).1
  let own := literal_exterior_owns_the_installed_head D S pad prior r CurrentExterior rfl
  let p := Q.paidChosen (publishedBank D S pad prior r) ack own
  p.steps+Q.paidChart.steps+3

theorem actual_written_row_uses_its_paid_setup_exactly_once :
    let old := paidOnWrittenRow D S pad prior sync reserved r written A
    let new := actualPaidOnWrittenRow D S pad prior sync reserved r written A Q
    new.result=old.result ∧
      new.steps=old.steps+actualSelectedSetupFee D S pad prior sync reserved r written A Q := by
  let p := entrySource (W:=W) D r
  have h := run_with_paid_bank_choice_has_R75_kernel_and_keeps_its_setup_debits
    D S pad prior r sync reserved written p.result rfl Q.paidChosen A.keep Q.paidChart A.layout A.retire
  dsimp only [p] at h
  rw [Q.chosenExact, Q.chartExact] at h
  dsimp only [actualPaidOnWrittenRow,paidOnWrittenRow,actualSelectedSetupFee]
  refine ⟨congrArg Prod.fst h.1,?_⟩
  rw [h.2]
  omega

#print axioms actual_written_row_uses_its_paid_setup_exactly_once
end
end J6R111SelectedGroup
