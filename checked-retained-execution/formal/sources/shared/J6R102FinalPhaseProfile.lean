import J6R102FinalPhasePhysicalClock

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
local instance profileDecision :
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

/-- Only measured local source operands. There is no field for an
active phase cap, a full scope cap or a complete core runtime. The
stopped-reader entry concerns the literal R65 result on the same
selected installed machine; R102/R94 provide source constructors. -/
structure MeasuredProfile
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (own : OwnsHeader X.header.result B)
    (K producerPower leafPower : ℕ) (coefficients : ProducerCoefficients) where
  current : CurrentLayoutSources T key prec tw bw Pg rank X.header.result
  fit : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (a : (SP).cutoff<c.edges),
    InputFits sel (readyAtPath T p a) rate
  chart : MountedChart T
  pointerWidth : ℕ
  tails : SavedDirectoryTails pointerWidth
  scope : MeasuredScopeInputs (withPaidOwnerLeaves X M basePos ord ownerInputs) B
  provider : ℕ
  prep : ℕ
  reader : ℕ
  seed : ℕ
  ingress : ℕ
  stopped : ∀ (z : Sigma (Path sel Ext)) (stop : z.1.edges ≤ (SP).cutoff),
    (readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) B z.2 stop).steps ≤
      combinedLeafBound (s:=s) (C:=C) X provider prep reader leafPower
  copyWidth : rank+1 ≤ K
  outerWidth : edgew ≤ K
  fixedWidth : scope.wordCaps.fixed ≤ K
  activeWords : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=rate) (r:=Ext) K
  centres : PrintedCentreScale s C K
  mount : ActualMountWidths (withPaidOwnerLeaves X M basePos ord ownerInputs) K seed
  offset : externalAddrWidth tc tj 0 ≤ K
  layoutShape : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
    letI := z.1.host.finiteEdge
    letI := z.1.host.finiteRow
    letI := z.1.host.finiteCol
    LayoutScales (current.atPath (withPaidOwnerLeaves X M basePos ord ownerInputs) B own z.2 a).input rank K
  rawDebit : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
    letI := z.1.host.finiteEdge
    (current.atPath (withPaidOwnerLeaves X M basePos ord ownerInputs) B own z.2 a).bytes.paid.steps ≤ ingress
  absoluteHigh : absolutePrecision s (Ext).edges (Ext).prec+
      (C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1)) ≤ K
  scopeGeometry : ScopeSizes s C (Ext).edges key prec tw bw Pg pointerWidth B.headers.length B.records.length
    scope.wordCaps scope.atlasSize K
  size : s ≤ K
  constant : C ≤ K
  truncation : ell ≤ K
  prec : (Ext).prec ≤ K
  vertices : vertexCount (Ext).host ≤ K
  individual : IndividualProducerBounds coefficients (leafHeight s) producerPower ingress provider
    scope.bootBudget scope.demandBudget scope.queryBudget scope.sourceWordBudget prep reader

theorem measured_profile_caps_the_given_source
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (own : OwnsHeader X.header.result B)
    (K producerPower leafPower : ℕ) (coefficients : ProducerCoefficients)
    (P : MeasuredProfile (rank:=rank) X M basePos ord ownerInputs B own K producerPower leafPower coefficients) :
    let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X :=
      fun b h a=>(P.current.exterior b h a).run
    let E := physicalExteriorInputs X layout
    let Q := proofDrivers R (P.current.retained P.fit) P.chart E B own
    let L := localClock s K producerPower leafPower coefficients
    CachedThreePhaseCaps Q (retireSavedDirectory P.tails) B L L L :=
  same_raw_clock_from_dimensions_and_individual_source_fees X M basePos ord ownerInputs B own P.current
    P.fit P.chart P.tails P.scope P.provider P.prep P.reader leafPower K P.seed P.ingress P.stopped
    P.copyWidth P.outerWidth P.fixedWidth P.activeWords P.centres P.mount P.offset P.layoutShape
    P.rawDebit P.absoluteHigh P.scopeGeometry P.size P.constant P.truncation P.prec P.vertices
    producerPower coefficients P.individual

#print axioms MeasuredProfile
#print axioms measured_profile_caps_the_given_source
end
end J6R102FinalPhase

