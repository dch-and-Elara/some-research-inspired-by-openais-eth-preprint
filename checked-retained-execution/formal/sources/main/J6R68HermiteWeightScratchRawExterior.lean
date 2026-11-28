import J6R68HermiteWeightScratchRawCore
import J6R68ActiveInputsSweepRun

/-! Connect the stock row to the physically marked root of the
actual raw recursion. Only that active entrance and one row are used;
this is not a transport of the old active supplier's Meter. -/
namespace J6R68.HermiteWeightScratch
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R23ScheduleWeight J6R24MeteredRecursion J6R49DFS J6R50NonModeScratch
open J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R58ActivePrep J6R62ActivePrep J6R63Active J6R64Active
open J6R66Active J6R51Online J6R52CacheWhole J6R48DFS J6R26DescriptorTree
open J6R50SourceProducer J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34ChildPath
open J6Mesh J6OrientedHost J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R24LegalLayout J6R31RootResidentTables J6R26StablePreparedRoot

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 16000000
set_option maxRecDepth 4650
set_option maxSynthPendingDepth 12

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

section PreparedStock
variable {f : ℤ[X]} {ell s q pw ew cw n : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f} {good : n≤2^f.natDegree}
local notation "A" => ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)
local notation "U" => ((printedParams (f:=f) (ell:=ell) s).levelWidth c.depth)

theorem actual_prepared_row_uses_its_raw_erase_roster
    (hq : 0<q) (fit : InputFits sel d q) (taperPos : 0<U) (taperSmall : U≤c.edges)
    (hf : f.Monic) (chart : MaskTable f.natDegree n good) (cover : physicalProbeCount f ell s c≤n)
    (header : Meter (CallWords c pw ew)) (layout : Meter (AtLayout sel d cw)) :
    let D := (prepare (bank:=bank) hq fit taperPos taperSmall hf chart cover header layout).result
    ∀ x : D.EmitRow,
      (D.fetch x).roster.rows=(eraseCentreKey x.val D.stock.rows).result.map (centreRowValue A) := by
  dsimp only
  intro x
  rfl
end PreparedStock

section ActualExterior
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell qr ro co e edgew tc tj key prec tw bw page s C q cw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable (X : StableExterior G ell qr ro co e edgew tc tj key prec tw bw)
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "Here" => (Path.root : Path sel
  (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Mch" => (OnlineMachine T key prec tw bw page q)

def rawExteriorActualReader
    (M : Mch) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (retire : J→ℕ) (B : L) (on : (S).cutoff<(Ext).edges) :
    ActiveChild (sel:=sel) (d:=readyAtPath T Here on) T.bank := fun t z β g=>
  let d := readyAtPath T Here on
  let w := addressed (sel:=sel) d t z β g
  project (bootWithHeader (M.initial w) retire (runRawAfter M F chart retire Ext Here w)
    (zeroM (T.bank (registerPrecision S Ext t) (register_positive d t)).hp) B)

theorem actual_raw_exterior_runs_the_exact_emitted_centre_row
    (M : Mch) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (layout : ExteriorLayout (T:=T) (page:=page) (cw:=cw) X)
    (retire : J→ℕ) (B : L) (own : OwnsHeader X.header.result B)
    (on : (S).cutoff<(Ext).edges) :
    let P := rootPrepare M F chart (physicalExteriorInputs X layout) B own on
    let D := P.result
    let hp := reachable_positive T (Here).reached
    let read := rawExteriorActualReader X M F chart retire B on
    let out := D.eval M.modeWidth hp T.vPositive X.hf read
    runRawPhysicalExterior X M F chart layout retire B own=⟨(out.result,B),P.steps+out.steps⟩ ∧
    (∀ x : D.EmitRow,
      let run := emittedCentreMeter D M.modeWidth hp T.vPositive X.hf read
      ∃ pre post,actualEmittedCentreRows D=pre++x::post ∧
        D.highRun M.modeWidth hp T.vPositive X.hf read=
          resumeUV (D.high hp).hp (pre.map run)
            (addM (D.high hp).hp (run x) (sumM (D.high hp).hp run post))) := by
  let P := rootPrepare M F chart (physicalExteriorInputs X layout) B own on
  let D := P.result
  let hp := reachable_positive T (Here).reached
  let read := rawExteriorActualReader X M F chart retire B on
  exact ⟨raw_root_uses_actual_sweep M F chart (physicalExteriorInputs X layout) retire B own on,
    fun x=>selected_stock_row_is_an_actual_sweep_operand D M.modeWidth hp T.vPositive X.hf read x⟩

end ActualExterior
end
#print axioms actual_prepared_row_uses_its_raw_erase_roster
#print axioms actual_raw_exterior_runs_the_exact_emitted_centre_row
end J6R68.HermiteWeightScratch
