import J6R71PairedResources
import J6R72SameRunLocalPeak
import J6R68AbsolutePrescribedR67
import J6R68RateJoint
import J6R68RecursivePeakTotal

/-! Combine the genuine printed exterior initialization and the paid
selected full-64 layout, on exactly the same R66 continuation and
R67 measured stopping/ownership phases. Neither a synthetic native
predecessor nor a separate complete layout tariff is supplied. -/
namespace J6R72SameRunLocalPeak
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
open J6R63Active J6R62ActivePrep J6R57ActiveFee J6R57ScopeFee J6R51Peak

open J6R50Peak J6R51Peak J6R52Peak J6R53PeakAddon J6R57LiveSpace J6R68.RecursivePeak
open J6R68.RetireScratch J6R68.MountFilterScratch J6R51ParentFrames J6R52CacheWhole J6R52CacheSource
open J6R49DFS J6R64Active J6ActiveSchedule

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
local instance exactJoinDecision :
    DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
      (exteriorChild G ell X.centre X.sample X.group)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)
local notation "R" => (withPaidOwnerLeaves X M basePos ord ownerInputs)

include boot in
theorem prescribed_physical_rate_and_selected_publication_mount_return_max
    (B : Bank) (rootLive : IsLive (X.seed pad) B) (own : OwnsHeader X.header.result B)
    (valid : ReadyOnStack (borns M) B) (supply : HasMeasuredOwnerInputs X M ownerInputs)
    (gateWidth : gate.created.val=base)
    (D : CurrentLayoutSources T key prec tw bw Pg rank X.header.result)
    (fitActive : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel Ext x) (a : (SP).cutoff<x.edges),
      InputFits sel (readyAtPath T p a) rate)
    {pointerWidth : ℕ} (tails : SavedDirectoryTails pointerWidth)
    (scopeInputs : MeasuredScopeInputs R B)
    (provider prep reader leafPower K seed baseFee ingressFee mask scale localPower : ℕ)
    (parts : MeasuredStopParts X M basePos ord ownerInputs B provider prep reader leafPower)
    (copyWidth : rank+1 ≤ K) (outerEdgeWidth : edgew ≤ K)
    (scopeFixedWidth : scopeInputs.wordCaps.fixed ≤ K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=rate) (r:=Ext) K)
    (cs : PrintedCentreScale s C K) (mount : ActualMountWidths R K seed)
    (offset : externalAddrWidth tc tj 0 ≤ K)
    (baseDebit : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      (preparedActive R z.2 a).steps ≤ baseFee)
    (targetShape : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      letI := z.1.host.finiteEdge
      letI := z.1.host.finiteRow
      letI := z.1.host.finiteCol
      LayoutScales (D.atPath R B own z.2 a).input rank K)
    (rawDebit : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      letI := z.1.host.finiteEdge
      (D.atPath R B own z.2 a).bytes.paid.steps ≤ ingressFee)
    (high : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      z.1.prec+(preparedActive R z.2 a).result.extraPrecision ≤ K)
    (masks : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges) t u,
      (((preparedActive R z.2 a).result.tape t).masks u).steps ≤ mask)
    (absolute : AbsoluteSeed s C (Ext))
    (numeric : combinedActualFixed (s:=s) (C:=C) X provider prep reader leafPower K mask baseFee (ingressFee+selectedLayoutRoof K+3)+
      (physicalAddressUnit K+measuredPerScope scopeInputs pointerWidth) ≤ scale*2^(localPower*LeafH))

    (shared pageBound fixed addr owner : Nat)
    (spaceWidth : rate ≤ uniformWidth s C)
    (pageFit : ExactPageFit
      (shadow R (D.retained fitActive)
        (physicalExteriorInputs X (fun b h a=>(D.exterior b h a).run)) B own) pageBound)
    (sizes : EntryWidths
      (shadow R (D.retained fitActive)
        (physicalExteriorInputs X (fun b h a=>(D.exterior b h a).run)) B own) fixed addr)
    (bootFit : BootBodyWidth
      (shadow R (D.retained fitActive)
        (physicalExteriorInputs X (fun b h a=>(D.exterior b h a).run)) B own) seed)
    (ownerFit : OwnerWidth
      (shadow R (D.retained fitActive)
        (physicalExteriorInputs X (fun b h a=>(D.exterior b h a).run)) B own) owner)
    (highSpace : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel Ext x) (a : (SP).cutoff<x.edges),
      x.prec+(liveActiveAt R (D.retained fitActive)
        (physicalExteriorInputs X (fun b h a=>(D.exterior b h a).run)) B own p a).result.extraPrecision ≤ K) :
    let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X :=
      fun b h a=>(D.exterior b h a).run
    let F := D.retained fitActive
    let E := physicalExteriorInputs X layout
    let ret : Job → Nat := retireSavedDirectory tails
    let out := runPhysicalExterior X R F layout ret B own
    let Q := shadow R F E B own
    let roof := recursiveResidentRoof shared B (Ext) pageBound K fixed addr seed owner s C+
      pathLimit s C*(prec+max edgew fixed+rate)+
      pathLimit s C*suspendedRosterCap s C (absolutePrecision s (Ext).edges (Ext).prec)
    ((T.frame (Here).reached).decode out.result.1=
      reduce (Ext).prec f ell ((Ext).host.contract X.hf) ∧ out.result.2=B ∧
      out.steps ≤ (pathLimit s C-(Ext).depth+1)*scale*2^((fullPrefixConstant C+localPower)*LeafH)) ∧
    (∀ {x : Call (PhysicalHost f ell)} (p : Path sel Ext x) (active : (SP).cutoff<x.edges)
      (t : Center SP x) (z : Probe SP x) (β : NativeMenu (N sel) x t) (g : Fin 64),
      let w := addressed (sel:=sel) (readyAtPath T p active) t z β g
      let next := Path.step p w
      let cut := observedReader R F tails B p active t z β g
      let words : TailCopyObservation pointerWidth := ⟨tails,tails⟩
      let H := localPeakRoof roof s C addr seed pointerWidth
      ∃ buf bits, ObservedRosterPause Q ret B next buf bits ∧
        project cut.1=liveReaderAt R F ret B p active t z β g ∧
        cut.2=some words ∧ cut.1.result.2=stackBank (borns R) B p ∧
        (∀ point, recursiveStagingBits R B p w shared buf point+
          literalControlPath R F E B own next+bits≤roof) ∧
        retireBits R F E B own p w shared buf bits words≤H ∧
        (∀ (_go : (SP).cutoff<((@Plan f ell s sel).child x w).edges) (j n : ℕ)
            (point : ChildWritePoint),
          let entered := sourceEntered R B p w
          let picked := observeSelection entered.site.birth.native.gWord j entered.site.birth.native.physical.raw
          let wrote := framesFromSelected entered.site.site entered.resident.rows picked.1.result
          (mountResident entered.site entered.resident).steps=picked.1.steps+wrote.steps+10 ∧
          max (recursiveStagingBits R B p w shared buf point+literalControlPath R F E B own next+bits)
            (max (max (filterBits R B p w shared buf j) (framePrefixBits R B p w shared buf n)+
                literalControlPath R F E B own next+bits)
              (retireBits R F E B own p w shared buf bits words))≤H)) := by
  let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X :=
    fun b h a=>(D.exterior b h a).run
  let F := D.retained fitActive
  let E := physicalExteriorInputs X layout
  let ret : Job → Nat := retireSavedDirectory tails
  let roof := recursiveResidentRoof shared B (Ext) pageBound K fixed addr seed owner s C+
    pathLimit s C*(prec+max edgew fixed+rate)+
    pathLimit s C*suspendedRosterCap s C (absolutePrecision s (Ext).edges (Ext).prec)
  have paired := J6R71PairedResources.prescribed_physical_run_rate_and_selected_peak
    X M basePos ord ownerInputs gate boot B rootLive own valid supply gateWidth D fitActive tails scopeInputs
    provider prep reader leafPower K seed baseFee ingressFee mask scale localPower parts
    copyWidth outerEdgeWidth scopeFixedWidth ws cs mount offset baseDebit targetShape rawDebit
    high masks absolute numeric shared pageBound fixed addr owner spaceWidth pageFit sizes bootFit ownerFit highSpace
  have ready : ReadyOnStack (borns R) B :=
    replacing_leaves_preserves_actual_ready_stack X M basePos ord ownerInputs B valid
  refine ⟨paired.1,?_⟩
  intro x p active t z β g
  let w := addressed (sel:=sel) (readyAtPath T p active) t z β g
  obtain ⟨buf,bits,observed,pub,entered⟩ := paired.2 p w
  have seen := actual_reader_returns_through_the_same_saved_tail_cut R F tails B ready p active t z β g
  let words : TailCopyObservation pointerWidth := ⟨tails,tails⟩
  have ranges := existing_live_path_bounds_mount_and_retirement_by_a_max
    R F E B own fixed addr seed shared buf bits roof sizes bootFit p w entered words
  refine ⟨buf,bits,observed,seen.1,seen.2.1,seen.2.2,pub,ranges.1,?_⟩
  intro go j n point
  have localCut := ranges.2 go j n
  exact ⟨localCut.1,Nat.max_le.mpr ⟨(pub point).trans (Nat.le_add_right _ _),localCut.2⟩⟩

#print axioms prescribed_physical_rate_and_selected_publication_mount_return_max
end
end J6R72SameRunLocalPeak
