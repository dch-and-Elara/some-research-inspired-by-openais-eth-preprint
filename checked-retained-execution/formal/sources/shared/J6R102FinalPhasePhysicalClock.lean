import J6R102FinalPhaseActual

/-! Expose the exact three R68 clock fields before recursion. Only the
actual stopped interpreter, actual selected setup, actual raw sweep,
and actual scoped source providers are used. This exposes the same
phase capsule that the frozen R68 top theorem constructs internally. -/
namespace J6R102FinalPhase
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
open J6R67UnifiedRate J6R68AbsolutePrescribed J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R63Active J6R62ActivePrep J6R57ActiveFee J6R57ScopeFee J6R51Peak J6R50Peak
open J6R79Numeric

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
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Job" => (PageJob f ell key prec tw bw (pageKeyWidth m+pad))
local instance clockExactDecision :
    DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
      (exteriorChild G ell X.centre X.sample X.group)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
local notation "R" => (withPaidOwnerLeaves X M basePos ord ownerInputs)

theorem same_raw_clock_from_dimensions_and_individual_source_fees
    (B : Bank) (own : OwnsHeader X.header.result B)
    (D : CurrentLayoutSources T key prec tw bw Pg rank X.header.result)
    (fitActive : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel Ext x) (a : (SP).cutoff<x.edges),
      InputFits sel (readyAtPath T p a) rate)
    (chart : MountedChart T)
    {pointerWidth : ℕ} (tails : SavedDirectoryTails pointerWidth)
    (scopeInputs : MeasuredScopeInputs R B)
    (provider prep reader leafPower K seed ingressFee : ℕ)
    (stopped : ∀ (z : Sigma (Path sel Ext)) (stop : z.1.edges ≤ (SP).cutoff),
      (readLeaf R B z.2 stop).steps ≤ combinedLeafBound (s:=s) (C:=C) X provider prep reader leafPower)
    (copyWidth : rank+1 ≤ K) (outerEdgeWidth : edgew ≤ K)
    (scopeFixedWidth : scopeInputs.wordCaps.fixed ≤ K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=rate) (r:=Ext) K)
    (cs : PrintedCentreScale s C K) (mount : ActualMountWidths R K seed)
    (offset : externalAddrWidth tc tj 0 ≤ K)
    (targetShape : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      letI := z.1.host.finiteEdge
      letI := z.1.host.finiteRow
      letI := z.1.host.finiteCol
      LayoutScales (D.atPath R B own z.2 a).input rank K)
    (rawDebit : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      letI := z.1.host.finiteEdge
      (D.atPath R B own z.2 a).bytes.paid.steps ≤ ingressFee)
    (absoluteHigh : absolutePrecision s (Ext).edges (Ext).prec+
      (C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1)) ≤ K)
    (scopeGeometry : ScopeSizes s C (Ext).edges key prec tw bw Pg pointerWidth B.headers.length B.records.length
      scopeInputs.wordCaps scopeInputs.atlasSize K)
    (hs : s ≤ K) (hC : C ≤ K) (he : ell ≤ K) (hr : (Ext).prec ≤ K) (hv : vertexCount (Ext).host ≤ K)
    (producerPower : ℕ) (coefficients : ProducerCoefficients)
    (actualProducers : IndividualProducerBounds coefficients (leafHeight s) producerPower ingressFee provider
      scopeInputs.bootBudget scopeInputs.demandBudget scopeInputs.queryBudget scopeInputs.sourceWordBudget prep reader) :
    let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X :=
      fun b h a=>(D.exterior b h a).run
    let E := physicalExteriorInputs X layout
    let Q := proofDrivers R (D.retained fitActive) chart E B own
    let L := localClock s K producerPower leafPower coefficients
    CachedThreePhaseCaps Q (retireSavedDirectory tails) B L L L := by
  have current := phases_on_the_exact_raw_runner X M basePos ord ownerInputs B own D fitActive chart tails scopeInputs
    provider prep reader leafPower K seed ingressFee stopped copyWidth outerEdgeWidth scopeFixedWidth ws cs mount
    offset targetShape rawDebit absoluteHigh
  have budget := each_actual_budget_below_the_same_printed_clock scopeInputs K pointerWidth scopeGeometry hs hC he hr hv
    ingressFee provider prep reader producerPower leafPower coefficients actualProducers
  exact widen_real_phase_caps_to_a_uniform_clock current budget.1 budget.2.1 budget.2.2

#print axioms same_raw_clock_from_dimensions_and_individual_source_fees
end
end J6R102FinalPhase

