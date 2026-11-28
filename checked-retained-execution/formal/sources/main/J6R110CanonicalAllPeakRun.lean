import J6R110CanonicalAllPeakActive
import J6R75RawPeakMaxPauseRun

/-! One actual R110 wrapper, one frozen raw runner and one R75 path
carry. Raw layout already charges the installed chart's grid.
We add the table to the resident carrier only for the old phases
whose field formulas do not already include it. -/
namespace J6R110CanonicalAllPeak
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
open J6R62ActivePrep J6R68ActiveInputs J6R68.LeafPeak.Packet J6R18ChildWrite
open J6R52Peak J6R54PeakInput J6R51Peak J6R57ScopeFee J6R66.BootPeak J6R50Peak
open J6R68.RetireScratch J6R72SameRunLocalPeak
open J6R75RawPeak J6R109CanonicalProbeTable J6R110CanonicalCoverage J6R110CanonicalMount

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 5100
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 41000000
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
local notation "Edeg" => f.natDegree
local notation "Nd" => (fullProbeDegree f.natDegree)
local notation "Nbits" => (fullProbeDegree f.natDegree+1)
local notation "Cap" => (full_probe_fit f.natDegree)
local notation "JetReserve" => (pathLimit s C*rawAncestorJetRoof
  s C ell f.natDegree (absolutePrecision s (Ext).edges (Ext).prec))

def ActualPaidCanonicalExteriorNamedPeak
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (D : CurrentLayoutSources T key prec tw bw Pg rank X.header.result)
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel Ext x) (a : (SP).cutoff<x.edges),
      InputFits sel (readyAtPath T p a) rate)
    (bytes : (canonicalTable Edeg Nbits).result=OldOrderedBytes Edeg Nd Cap)
    {width : ℕ} (tails : SavedDirectoryTails width) (B : Bank) (own : OwnsHeader X.header.result B)
    (shared pageBound fixed addr seed owner : ℕ) : Prop :=
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let F := D.retained fit
  let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X := fun b h a=>(D.exterior b h a).run
  let E := physicalExteriorInputs X layout
  let chart := (mountFullChart T bytes).result
  let nextEntry := runRawExteriorWithPaidCanonicalChart X Nd Cap bytes
    (canonical_mount_coverage_from_original_prepared T) R F layout (retireSavedDirectory tails) B own
  let raw := runRawPhysicalExterior X R F chart layout (retireSavedDirectory tails) B own
  let table := gridMemoryBits chart.table.raw
  let charged := shared+table
  let bootAmbient := shared+mountedSelectedBits B
  let room := rawCarrierRoof charged B Ext pageBound fixed addr seed owner s C rate
  let bare := rawCarrierRoof shared B Ext pageBound fixed addr seed owner s C rate
  let jet := fun {x : Call (PhysicalHost f ell)} (p : Path sel Ext x) => exactAncestorJetWidth R F chart E B own p
  nextEntry=⟨raw.result,wholeMountedDebit Edeg (2^Edeg)+raw.steps+3⟩ ∧ nextEntry.result.2=B ∧
  table=Edeg*2^Edeg ∧ table≤128*s^5 ∧
  ActualRawExteriorMaximalNamedPause X M basePos ord ownerInputs D fit chart tails B own
    shared pageBound fixed addr seed owner ∧
  ((Ext).edges≤(SP).cutoff →
    SameRawOriginalRootStop X M basePos ord ownerInputs F chart layout tails B own charged) ∧
  ∃ carry : ∀ {j : Call (PhysicalHost f ell)},Path sel Ext j→ℕ,
    (∀ {j : Call (PhysicalHost f ell)} (p : Path sel Ext j),
      ActualRawAncestorStack R F chart E B own tails p (carry p) ∧
      ActualRawJetSupplement R F chart E B own tails p (carry p) (jet p) ∧
      recursiveResidentBits charged R B p (carry p)+jet p≤room+JetReserve ∧
      (∀ built, CanonicalBootCut T bytes built →
        max (bootAmbient+built) (recursiveResidentBits charged R B p (carry p)+jet p)≤
          max (bootAmbient+264*s^5) (room+JetReserve)) ∧
      SameRawActualInverseCuts R F chart E B own tails charged pageBound fixed addr seed owner
        p (carry p) (jet p) ∧
      ∀ on : (SP).cutoff<j.edges,
        CanonicalActiveCutMaxima D R B own (readExterior X) fit bytes p on shared (carry p) (bare+JetReserve)) ∧
    ∀ {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) (w : (P).Slot j),
      let next := Path.step p w
      let total := recursiveResidentBits charged R B next (carry next)+jet next
      let oldScope := room+max ((2*(C*s))*(addr+sourceBodyCap s C seed)) (4*width)+JetReserve
      SameRawScopeWithJets R F chart B tails charged pageBound fixed addr seed owner
        p w (carry next) (jet next) ∧
      (((P).child j w).edges≤(SP).cutoff → ((P).child j w).edges=0 →
        SameRawOriginalZeroStop X M basePos ord ownerInputs F chart tails B p w total (room+JetReserve)) ∧
      (∀ stop : ((P).child j w).edges≤(SP).cutoff,0<((P).child j w).edges →
        SameRawOriginalPositiveStop X M basePos ord ownerInputs F chart tails B p w stop total (room+JetReserve)) ∧
      ∀ (_active : (SP).cutoff<((P).child j w).edges) (i k : ℕ) (point : ChildWritePoint)
        (built : ℕ), CanonicalBootCut T bytes built →
        let stage := recursiveStagingBits R B p w charged (carry next) point
        let f0 := filterBits R B p w charged (carry next) i
        let f1 := framePrefixBits R B p w charged (carry next) k
        let ret := trueRawReturnWithCarry R B p w charged (carry next)
          (⟨tails,tails⟩ : TailCopyObservation width)
        let paused := max stage (max (max f0 f1) ret)+jet next
        max (bootAmbient+built) paused ≤ max (bootAmbient+264*s^5) oldScope

/-- Paid canonical table startup and the original recursive named
pauses of the literal same exterior; the checked byte-order bridge
remains a premise. The table enters the no-chart old carriers once.
The existing layout phases retain their original, explicit grid
charge rather than receiving a second copy in the carrier. -/
theorem paper6_actual_paid_canonical_exterior_has_named_phase_maximum
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
    (D : CurrentLayoutSources T key prec tw bw Pg rank X.header.result)
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel Ext x) (a : (SP).cutoff<x.edges),
      InputFits sel (readyAtPath T p a) rate)
    (bytes : (canonicalTable Edeg Nbits).result=OldOrderedBytes Edeg Nd Cap)
    {width : ℕ} (tails : SavedDirectoryTails width) (B : Bank) (own : OwnsHeader X.header.result B)
    (live : IsLive (X.seed pad) B) (valid : ReadyOnStack (borns M) B)
    (modeFits : rate≤uniformWidth s C) (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (shared pageBound fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit (withPaidOwnerLeaves X M basePos ord ownerInputs) pageBound)
    (sizes : EntryWidths (withPaidOwnerLeaves X M basePos ord ownerInputs) fixed addr)
    (bootFit : BootBodyWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) seed)
    (owners : OwnerWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) owner) :
    ActualPaidCanonicalExteriorNamedPeak X M basePos ord ownerInputs D fit bytes tails B own
      shared pageBound fixed addr seed owner := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let F := D.retained fit
  let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X := fun b h a=>(D.exterior b h a).run
  let E := physicalExteriorInputs X layout
  let chart := (mountFullChart T bytes).result
  let raw := runRawPhysicalExterior X R F chart layout (retireSavedDirectory tails) B own
  let nextEntry := runRawExteriorWithPaidCanonicalChart X Nd Cap bytes
    (canonical_mount_coverage_from_original_prepared T) R F layout (retireSavedDirectory tails) B own
  let table := gridMemoryBits chart.table.raw
  let charged := shared+table
  let bootAmbient := shared+mountedSelectedBits B
  let room := rawCarrierRoof charged B Ext pageBound fixed addr seed owner s C rate
  let jet := fun {x : Call (PhysicalHost f ell)} (p : Path sel Ext x) => exactAncestorJetWidth R F chart E B own p
  have old := paper6_same_raw_exterior_has_the_maximal_named_candidate_pauses X M basePos ord ownerInputs
    gate boot D fit chart tails B own live valid modeFits supply gateWidth shared pageBound fixed addr seed owner
    pageFit sizes bootFit owners
  have identity := old
  obtain ⟨restore,_,carry,paths,_⟩ := identity
  obtain ⟨_,_,_,measure,_,length,lengthCap,_,_⟩ :=
    actual_full_mount_has_one_printed_polynomial_fee_and_selected_workspace T bytes
  have wired : nextEntry=⟨raw.result,wholeMountedDebit Edeg (2^Edeg)+raw.steps+3⟩ := by
    change (⟨raw.result,(mountFullChart T bytes).steps+raw.steps+3⟩ : Meter _) = _
    rw [measure]
  have legal : ReadyOnStack (borns R) B := by
    change ReadyOnStack (borns (withPaidOwnerLeaves X M basePos ord ownerInputs)) B
    rw [paid_owner_leaf_keeps_births X M basePos ord ownerInputs]
    exact valid
  have jetFit {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) : jet p≤JetReserve :=
    (exact_raw_ancestor_jet_width_fits_and_is_observed R F chart E B own tails p (carry p) (paths p).1).2
  have counted {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) :
      recursiveResidentBits charged R B p (carry p)+jet p≤room+JetReserve :=
    Nat.add_le_add (raw_ancestor_and_same_physical_carrier_fit_together
      R F chart E B own tails charged pageBound fixed addr seed owner pageFit sizes bootFit owners
      p (carry p) (paths p).1) (jetFit p)
  have returned : nextEntry.result.2=B := by
    change raw.result.2=B
    exact restore
  refine ⟨wired,returned,length,lengthCap,old,?_,carry,?_,?_⟩
  · intro stop
    exact same_physical_raw_root_stop_has_all_named_clock_cuts
      X M basePos ord ownerInputs F chart layout tails B own live stop charged
  · intro j p
    refine ⟨(paths p).1,(paths p).2.1,counted p,?_,?_,?_⟩
    · intro built cut
      exact same_entry_boot_and_regional_pause_take_maximum T bytes bootAmbient built _ _ cut (counted p)
    · exact same_raw_active_path_has_the_named_inverse_cuts
        R F chart E B own tails charged pageBound fixed addr seed owner pageFit sizes bootFit owners
        p (carry p) (jet p) (paths p).1 (jetFit p)
    · intro on
      exact actual_input_layout_and_scan_do_not_duplicate_the_paid_chart D R B own (readExterior X) fit
        bytes p on shared (carry p) _ (paths p).2.2.1 ((paths p).2.2.2.2 on)
  · intro j p w next total scopeRoom
    have scope := actual_raw_scope_cuts_keep_the_fixed_ancestor_half_jets R F chart E B own tails legal
      charged pageBound fixed addr seed owner pageFit sizes bootFit owners
      p w (carry next) (jet next) (paths next).1 (jetFit next)
    refine ⟨scope,?_,?_,?_⟩
    · intro stop hZero
      exact same_raw_zero_stop_has_all_named_clock_cuts X M basePos ord ownerInputs F chart tails B live valid
        p w stop hZero total (room+JetReserve) (counted next)
    · intro stop positive
      exact same_raw_positive_stop_has_all_named_clock_cuts X M basePos ord ownerInputs gate boot F E chart tails
        B own live valid supply gateWidth p w stop positive total (room+JetReserve) (counted next)
    · intro active i k point built cut
      exact same_entry_boot_and_regional_pause_take_maximum T bytes bootAmbient built _ _ cut
        (scope.2.2.2.2.2 active i k point).2

#print axioms paper6_actual_paid_canonical_exterior_has_named_phase_maximum
end
end J6R110CanonicalAllPeak
