import J6R110CanonicalMountCore
import J6R68ActiveInputsSweepRun

/-! The generated chart is a physical input to the exact existing raw
exterior evaluator. It is not a differently ordered evaluation followed
by a semantic output comparison. There is one table generation/install
before the call; every native read consumes this installed result. -/
namespace J6R110CanonicalMount
open scoped Polynomial
open Polynomial AOracleMachineTime J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R26DescriptorTree J6R49DFS
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer J6R51Online
open J6R58ActivePrep J6R62ActivePrep J6R63Active J6R64Active J6R66Active J6R68ActiveInputs.Sweep
open J6R109CanonicalProbeTable J6Mesh J6OrientedHost J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R24LegalLayout J6R31RootResidentTables J6R26StablePreparedRoot

set_option autoImplicit false
set_option diagnostics true
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16500000
set_option maxRecDepth 4200
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
section Chart
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}

/-- A finite printed upper bound on the table size. It is not a mask
oracle; it merely proves that every actual native request has a row. -/
def Covers (d : ℕ) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (_p : Path sel r x) (_ : (printedParams (f:=f) (ell:=ell) s).cutoff<x.edges),
    physicalProbeCount f ell s x≤d+1

variable (T : Prepared cfg sel r hf)
variable (d : ℕ) (fit : d+1≤2^f.natDegree)
variable (bytes : (canonicalTable f.natDegree (d+1)).result=OldOrderedBytes f.natDegree d fit)
variable (covers : Covers (sel:=sel) (r:=r) d)

def mountCanonicalChart : Meter (MountedChart T) :=
  let table := mountCanonicalTable f.natDegree d fit bytes
  ⟨⟨d+1,fit,table.result,covers⟩,table.steps+3⟩

theorem mounted_chart_is_the_paid_table_and_captured_once (positive : 0<f.natDegree) :
    let chart := mountCanonicalChart T d fit bytes covers
    chart.result.table.raw=(canonicalTable f.natDegree (d+1)).result ∧
    chart.steps=canonicalTableFee f.natDegree (d+1)+(2+(d+1)*(3*f.natDegree+5))+4+3 := by
  have entry := actual_mount_is_one_counter_and_one_copy f.natDegree d positive fit bytes
  exact ⟨entry.1,congrArg (·+3) entry.2⟩

end Chart

section Exterior
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell qr ro co e edgew tc tj key prec tw bw page s C q cw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable (X : StableExterior G ell qr ro co e edgew tc tj key prec tw bw)
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (d : ℕ) (fit : d+1≤2^f.natDegree)
variable (bytes : (canonicalTable f.natDegree (d+1)).result=OldOrderedBytes f.natDegree d fit)
variable (covers : Covers (sel:=sel) (r:=exteriorChild G ell X.centre X.sample X.group) d)
variable (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
variable (layout : ExteriorLayout (T:=T) (page:=page) (cw:=cw) X)
variable (retire : PageJob f ell key prec tw bw page→ℕ) (B : PageBank f ell key prec tw bw page)
variable (own : OwnsHeader X.header.result B)

/-- Run only the existing physical evaluator with the mounted result.
The existing exterior Page bank is not republished or reinstalled. -/
def runRawExteriorWithPaidCanonicalChart :
    Meter (J6R24MeteredRecursion.Block (T.frame (Path.root : Path sel
      (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)).reached) ell× PageBank f ell key prec tw bw page) :=
  let chart := mountCanonicalChart T d fit bytes covers
  let out := J6R68ActiveInputs.Sweep.runRawPhysicalExterior (T:=T) X M F chart.result layout retire B own
  Meter.mk out.result (chart.steps+out.steps+3)

theorem raw_runner_consumes_this_actual_mount_once (positive : 0<f.natDegree) :
    let chart := mountCanonicalChart T d fit bytes covers
    let run := J6R68ActiveInputs.Sweep.runRawPhysicalExterior (T:=T) X M F chart.result layout retire B own
    runRawExteriorWithPaidCanonicalChart X d fit bytes covers M F layout retire B own =
      Meter.mk run.result (canonicalTableFee f.natDegree (d+1)+(2+(d+1)*(3*f.natDegree+5))+4+3+run.steps+3) := by
  have paid := (mounted_chart_is_the_paid_table_and_captured_once T d fit bytes covers positive).2
  unfold runRawExteriorWithPaidCanonicalChart
  dsimp only
  rw [paid]

end Exterior
#print axioms mounted_chart_is_the_paid_table_and_captured_once
#print axioms raw_runner_consumes_this_actual_mount_once
end
end J6R110CanonicalMount