import J6R75RawPeakAggregate
import J6R75RawPeakMaxPausePath

/-! A single old named-phase witness supplies the carrier for every
literal greedy candidate pause of the exact same physical exterior.
The terminal and scope observations are not recomputed on another
runner. Each local controlled scan gives a maximum with any old
selected phase bound, never a sum over candidates or different
phases. The mounted mask table is an input of this execution. -/
namespace J6R75RawPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active J6R53TerminalGate
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R30ProducedGateRegistry J6R68.RecursivePeak J6R68ActiveInputs.Sweep
open J6R62ActivePrep J6R68ActiveInputs J6R68.LeafPeak.Packet J6R21Ancestor J6R50Leaf J6R62Leaf J6R18ChildWrite
open J6R52Peak J6R54PeakInput J6R51Peak J6R57ScopeFee J6R66.BootPeak
open J6R35RootOrigins J6R34ChildPath J6R50Peak J6R30ProducedGateRegistry
open J6R68.RetireScratch J6R72SameRunLocalPeak
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 34000000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Mach" => (OnlineMachine T key prec tw bw Pg rate)
local notation "JetReserve" => (pathLimit s C*rawAncestorJetRoof
  s C ell f.natDegree (absolutePrecision s (Ext).edges (Ext).prec))

/-- Extend the old named phase peak without choosing a different path
carrier. For every real vertex pause and legal candidate the bound is
explicit in ControlledLayoutPathPause/ControlledCandidatePause:
carrier roof, actual layout ingress/header/masks, one control reserve
and one M² pair/tally workspace. Old pause limits need not be increased. -/
def ActualRawExteriorMaximalNamedPause
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (D : CurrentLayoutSources T key prec tw bw Pg rank X.header.result)
    (fit : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (on : (SP).cutoff<c.edges),
      InputFits sel (readyAtPath T p on) rate)
    (chart : MountedChart T) {width : ℕ} (tails : SavedDirectoryTails width)
    (B : Bank) (own : OwnsHeader X.header.result B) (shared pageBound fixed addr seed owner : ℕ) : Prop :=
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let F := D.retained fit
  let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X := fun b h on=>(D.exterior b h on).run
  let E := physicalExteriorInputs X layout
  let roof := rawCarrierRoof shared B Ext pageBound fixed addr seed owner s C rate+JetReserve
  let jet := fun {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) =>
    exactAncestorJetWidth R F chart E B own p
  (runRawPhysicalExterior X R F chart layout (retireSavedDirectory tails) B own).result.2=B ∧
  ((Ext).edges≤(SP).cutoff →
    SameRawOriginalRootStop X M basePos ord ownerInputs F chart layout tails B own shared) ∧
  ∃ carry : ∀ {j : Call (PhysicalHost f ell)},Path sel Ext j → ℕ,
    (∀ {j : Call (PhysicalHost f ell)} (p : Path sel Ext j),
      ActualRawAncestorStack R F chart E B own tails p (carry p) ∧
      ActualRawJetSupplement R F chart E B own tails p (carry p) (jet p) ∧
      recursiveResidentBits shared R B p (carry p)+jet p≤roof ∧
      SameRawActualInverseCuts R F chart E B own tails shared pageBound fixed addr seed owner
        p (carry p) (jet p) ∧
      ∀ on : (SP).cutoff<j.edges,
        ControlledLayoutPathPause D R chart B own (readExterior X) fit p on shared (carry p) roof) ∧
    ∀ {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) (w : (P).Slot j),
      let next := Path.step p w
      let total := recursiveResidentBits shared R B next (carry next)+jet next
      SameRawScopeWithJets R F chart B tails shared pageBound fixed addr seed owner p w (carry next) (jet next) ∧
      (((P).child j w).edges≤(SP).cutoff → ((P).child j w).edges=0 →
        SameRawOriginalZeroStop X M basePos ord ownerInputs F chart tails B p w total roof) ∧
      (∀ (stop : ((P).child j w).edges≤(SP).cutoff),0<((P).child j w).edges →
        SameRawOriginalPositiveStop X M basePos ord ownerInputs F chart tails B p w stop total roof)

theorem paper6_same_raw_exterior_has_the_maximal_named_candidate_pauses
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
    (D : CurrentLayoutSources T key prec tw bw Pg rank X.header.result)
    (fit : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (on : (SP).cutoff<c.edges),
      InputFits sel (readyAtPath T p on) rate)
    (chart : MountedChart T) {width : ℕ} (tails : SavedDirectoryTails width)
    (B : Bank) (own : OwnsHeader X.header.result B) (live : IsLive (X.seed pad) B)
    (valid : ReadyOnStack (borns M) B) (modeFits : rate≤uniformWidth s C)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (shared pageBound fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit (withPaidOwnerLeaves X M basePos ord ownerInputs) pageBound)
    (sizes : EntryWidths (withPaidOwnerLeaves X M basePos ord ownerInputs) fixed addr)
    (bootFit : BootBodyWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) seed)
    (owners : OwnerWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) owner) :
    ActualRawExteriorMaximalNamedPause X M basePos ord ownerInputs D fit chart tails B own
      shared pageBound fixed addr seed owner := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X := fun b h on=>(D.exterior b h on).run
  let F := D.retained fit
  let E := physicalExteriorInputs X layout
  let roof := rawCarrierRoof shared B Ext pageBound fixed addr seed owner s C rate+JetReserve
  obtain ⟨restored,rootStop,carry,anc,slots⟩ := paper6_actual_raw_exterior_selected_phase_peak
    X M basePos ord ownerInputs gate boot F chart layout tails B own live valid modeFits supply gateWidth
    shared pageBound fixed addr seed owner pageFit sizes bootFit owners
  refine ⟨restored,rootStop,carry,?_,slots⟩
  intro j p
  obtain ⟨history,jets,cap,inv⟩ := anc p
  refine ⟨history,jets,cap,inv,?_⟩
  intro a
  have bound : recursiveResidentBits shared R B p (carry p)+
      exactAncestorJetWidth R F chart (D.rootInputs (readExterior X)) B own p≤roof := cap
  exact actual_selected_path_observes_its_controlled_original_greedy_pause D R chart B own
    (readExterior X) fit p a shared (carry p) roof bound

#print axioms paper6_same_raw_exterior_has_the_maximal_named_candidate_pauses
end
end J6R75RawPeak
