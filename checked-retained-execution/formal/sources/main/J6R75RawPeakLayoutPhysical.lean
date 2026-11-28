import J6R75RawPeakLayoutPath
import J6R75RawPeakMaskPath

/-! Match the actual physical-exterior call in the raw time theorem
with the same selected layout and mask workspace declarations. This
is a definitional source specialization, not a time or value transfer. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R65LeafRate J6R30ProducedGateRegistry
open J6R67UnifiedRate J6R68AbsolutePrescribed J6R68ActiveInputs
open J6R63Active J6R62ActivePrep J6R57ActiveFee J6R57ScopeFee J6R51Peak J6R50Peak
open J6R68ActiveInputs.Sweep J6R17ModeTape J6R9Recursive V8NativeMessage.N2DLabels
open J6R68.RecursivePeak J6R66.BootPeak J6R54PeakInput

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 24500000
set_option maxRecDepth 4450
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Here" => (Path.root : Path sel
  (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
local notation "LeafH" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Job" => (PageJob f ell key prec tw bw (pageKeyWidth m+pad))
variable {c : Call (PhysicalHost f ell)}
local notation "P" => (@Plan f ell s sel)
local notation "Mach" => (OnlineMachine T key prec tw bw Pg rate)

local instance physicalLayoutEdges : Fintype c.host.Edge := c.host.finiteEdge
local instance physicalLayoutRows : Fintype c.host.Row := c.host.finiteRow
local instance physicalLayoutCols : Fintype c.host.Col := c.host.finiteCol

theorem same_literal_raw_exterior_uses_chosen_physical_layout_workspace
    (D : CurrentLayoutSources T key prec tw bw Pg rank X.header.result)
    (R : Mach) (chart : MountedChart T) (B : Bank) (own : OwnsHeader X.header.result B)
    (fitActive : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel Ext x) (on : (SP).cutoff<x.edges),
      InputFits sel (readyAtPath T p on) rate)
    (p : Path sel Ext c) (on : (SP).cutoff<c.edges) (shared carry roof : ℕ)
    (h : recursiveResidentBits shared R B p carry+
      exactAncestorJetWidth R (D.retained fitActive) chart
        (D.rootInputs (readExterior X)) B own p≤roof) :
    let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X :=
      fun b h on=>(D.exterior b h on).run
    let F := D.retained fitActive
    let E := physicalExteriorInputs X layout
    let input := literalStockCapturesAt R F E B own p on
    let words := input.2.1.result
    let W := D.atPath R B own p on
    let actual := runWithIngress W.input rank W.bytes
    let resident := recursiveResidentBits shared R B p carry+exactAncestorJetWidth R F chart E B own p
    (∀ retire,runRawPhysicalExterior X R F chart layout retire B own=runRawRoot R F chart E retire B own) ∧
    input.2.2=W.run ∧
    input.2.2.result.boxes=actual.result.boxes ∧
    input.2.2.result.copies.bits=actual.result.copies ∧
    LiteralRawLayoutPhases W.input W.bytes rank (wordsOf (packing sel (readyAtPath T p on)))
      (resident+(words.precision.bits.length+words.edges.bits.length+gridMemoryBits chart.table.raw))
      (roof+(prec+input.1+f.natDegree*chart.count)) := by
  refine ⟨fun _=>rfl,?_⟩
  exact actual_raw_path_layout_uses_one_original_physical_workspace D R chart B own (readExterior X)
    fitActive p on shared carry roof h

#print axioms same_literal_raw_exterior_uses_chosen_physical_layout_workspace
end
end J6R75RawPeak
