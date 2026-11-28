import J6R116ReadyRetainedPayload
import J6R110CanonicalCoverageMount

/-! Inputs to the retained continuation of one actually admitted request.
This is data and original source guards, not a scalar answer or an oracle. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R49Leaf J6R57Public J6R34OfficialGateway
open J6R57PublicRequest J6R54PublicFamily J6R52FreshExterior J6OrientedHostEval

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 5300
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj kp prec tw bw : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {Cpt : Compiled G ell q ro co de prec kp bw} {pad : ℕ}

variable (admitted : ResidentAdmissionCarry (W:=W) Cpt pad)
local notation "R" => (exteriorChild G ell admitted.site.centre admitted.site.sample admitted.site.group)

open J6R110CanonicalCoverage J6R110CanonicalMount J6R109CanonicalProbeTable

variable (preparation : Meter (ReadyRetainedPayload admitted))
variable (ordered : (canonicalTable f.natDegree (fullProbeDegree f.natDegree+1)).result=
  OldOrderedBytes f.natDegree (fullProbeDegree f.natDegree) (full_probe_fit f.natDegree))

/-- Only the chart field is replaced. The actual earlier preparation and
its complete bill are retained. The returned chart is exactly the one
used by every retained child, not a value-only comparison with a chart. -/
def prepareWithPaidOriginalOrder : Meter (ReadyRetainedPayload admitted) :=
  let A := preparation.result
  let chart := mountFullChart A.prepared ordered
  let actual := {A.drivers with masks := chart.result}
  ⟨{A with drivers := actual},preparation.steps+chart.steps+4⟩

theorem the_retained_driver_uses_the_one_paid_chart_and_its_printed_bound :
    let chart := mountFullChart preparation.result.prepared ordered
    let out := prepareWithPaidOriginalOrder admitted preparation ordered
    out.result.drivers.masks=chart.result ∧
      out.steps=preparation.steps+chart.steps+4 ∧
      out.steps≤preparation.steps+3660*preparation.result.size^5+4 := by
  have h := (actual_full_mount_has_one_printed_polynomial_fee_and_selected_workspace
    preparation.result.prepared ordered).2.2.2.2.1
  exact ⟨rfl,rfl,Nat.add_le_add_right (Nat.add_le_add_left h preparation.steps) 4⟩

#print axioms prepareWithPaidOriginalOrder
#print axioms the_retained_driver_uses_the_one_paid_chart_and_its_printed_bound
end
end J6R111KeptOwnerFlow

