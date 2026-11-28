import J6R75RawPeakTerminalAttach
import J6R75RawPeakJetCanonical
import J6R75RawPeakScopeJet
import J6R75RawPeakHermiteJet

/-! One matched exterior execution for the already measured phases.
All started paths use the same resident carry function and the exact
half-jet widths of the same raw ancestor frames. This is a selected
payload theorem, not an allocator or an unmodeled setup bound. -/
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
open J6R64Active J6R66Active J6R30ProducedGateRegistry J6R68.RecursivePeak J6R68.LeafPeak J6R68ActiveInputs.Sweep
open J6R68.LeafPeak.Packet J6R21Ancestor J6R50Leaf J6R62Leaf J6R18ChildWrite
open J6R52Peak J6R54PeakInput J6R51Peak J6R57ScopeFee J6R66.BootPeak
open J6R35RootOrigins J6R34ChildPath J6R50Peak J6R30ProducedGateRegistry
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4950
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 26000000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {c : Call (PhysicalHost f ell)}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Job" => (PageJob f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Here" => (Path.root : Path sel Ext Ext)
local notation "Mach" => (OnlineMachine T key prec tw bw Pg rate)

local notation "JetReserve" => (pathLimit s C*rawAncestorJetRoof
  s C ell f.natDegree (absolutePrecision s (Ext).edges (Ext).prec))

def ActualRawExteriorNamedPhasePeak
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (chart : MountedChart T)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    {width : ℕ} (tails : SavedDirectoryTails width)
    (B0 : Bank) (own : OwnsHeader X.header.result B0)
    (shared pageBound fixed addr seed owner : ℕ) : Prop :=
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let E := physicalExteriorInputs X layout
  let roof := rawCarrierRoof shared B0 Ext pageBound fixed addr seed owner s C rate+JetReserve
  let jet := fun {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) =>
    exactAncestorJetWidth R F chart E B0 own p
  (runRawPhysicalExterior X R F chart layout (retireSavedDirectory tails) B0 own).result.2=B0 ∧
  ((Ext).edges≤(SP).cutoff →
    SameRawOriginalRootStop X M basePos ord ownerInputs F chart layout tails B0 own shared) ∧
  ∃ carry : ∀ {j : Call (PhysicalHost f ell)},Path sel Ext j → ℕ,
    (∀ {j : Call (PhysicalHost f ell)} (p : Path sel Ext j),
      ActualRawAncestorStack R F chart E B0 own tails p (carry p) ∧
      ActualRawJetSupplement R F chart E B0 own tails p (carry p) (jet p) ∧
      recursiveResidentBits shared R B0 p (carry p)+jet p≤roof ∧
      SameRawActualInverseCuts R F chart E B0 own tails shared pageBound fixed addr seed owner
        p (carry p) (jet p)) ∧
    ∀ {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) (w : (P).Slot j),
      let next := Path.step p w
      let total := recursiveResidentBits shared R B0 next (carry next)+jet next
      SameRawScopeWithJets R F chart B0 tails shared pageBound fixed addr seed owner
        p w (carry next) (jet next) ∧
      (((P).child j w).edges≤(SP).cutoff → ((P).child j w).edges=0 →
        SameRawOriginalZeroStop X M basePos ord ownerInputs F chart tails B0 p w total roof) ∧
      (∀ (stop : ((P).child j w).edges≤(SP).cutoff),0<((P).child j w).edges →
        SameRawOriginalPositiveStop X M basePos ord ownerInputs F chart tails B0 p w stop total roof)

/-- Same literal `runRawPhysicalExterior` and same mount/retire/leaf
providers as the raw-sweep time theorem. The observations are exactly
publication, mount filter and frame prefix, retire, the real raw
Hermite inverse, root/zero/positive stop clocks, and packet preparation,
choice DFS, resize, and the last V multiply on those clocks.

The remaining source chart/input-production and non-enumerated
arithmetic temporaries are not charged as zero, nor is the ambient
runtime heap part of this selected-encoding theorem. -/
theorem paper6_actual_raw_exterior_selected_phase_peak
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
    (F : RetainedAfter T key prec tw bw Pg rate cw) (chart : MountedChart T)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    {width : ℕ} (tails : SavedDirectoryTails width)
    (B0 : Bank) (own : OwnsHeader X.header.result B0) (live : IsLive (X.seed pad) B0)
    (valid : ReadyOnStack (borns M) B0) (modeFits : rate≤uniformWidth s C)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (shared pageBound fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit (withPaidOwnerLeaves X M basePos ord ownerInputs) pageBound)
    (sizes : EntryWidths (withPaidOwnerLeaves X M basePos ord ownerInputs) fixed addr)
    (bootFit : BootBodyWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) seed)
    (owners : OwnerWidth (withPaidOwnerLeaves X M basePos ord ownerInputs) owner) :
    ActualRawExteriorNamedPhasePeak X M basePos ord ownerInputs F chart layout tails B0 own
      shared pageBound fixed addr seed owner := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let E := physicalExteriorInputs X layout
  have legal : ReadyOnStack (borns R) B0 := by
    change ReadyOnStack (borns (withPaidOwnerLeaves X M basePos ord ownerInputs)) B0
    rw [paid_owner_leaf_keeps_births X M basePos ord ownerInputs]
    exact valid
  let roof := rawCarrierRoof shared B0 Ext pageBound fixed addr seed owner s C rate+JetReserve
  let possible := fun {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) =>
    every_raw_path_has_a_named_suspended_ancestor_budget R F chart E B0 own tails legal modeFits p
  let carry := fun {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) => Classical.choose (possible p)
  have observed {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) :
      ActualRawAncestorStack R F chart E B0 own tails p (carry p) :=
    (Classical.choose_spec (possible p)).1
  have jets {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) :
      ActualRawJetSupplement R F chart E B0 own tails p (carry p)
        (exactAncestorJetWidth R F chart E B0 own p) ∧
      exactAncestorJetWidth R F chart E B0 own p≤JetReserve :=
    exact_raw_ancestor_jet_width_fits_and_is_observed R F chart E B0 own tails p (carry p) (observed p)
  have room {j : Call (PhysicalHost f ell)} (p : Path sel Ext j) :
      recursiveResidentBits shared R B0 p (carry p)+exactAncestorJetWidth R F chart E B0 own p≤roof :=
    Nat.add_le_add (raw_ancestor_and_same_physical_carrier_fit_together
      R F chart E B0 own tails shared pageBound fixed addr seed owner
      pageFit sizes bootFit owners p (carry p) (observed p)) (jets p).2
  refine ⟨raw_root_restores_actual_bank R F chart E (retireSavedDirectory tails) B0 own,
    fun stop=>same_physical_raw_root_stop_has_all_named_clock_cuts
      X M basePos ord ownerInputs F chart layout tails B0 own live stop shared,carry,?_,?_⟩
  · intro j p
    exact ⟨observed p,(jets p).1,room p,
      same_raw_active_path_has_the_named_inverse_cuts R F chart E B0 own tails
        shared pageBound fixed addr seed owner pageFit sizes bootFit owners p (carry p)
        (exactAncestorJetWidth R F chart E B0 own p) (observed p) (jets p).2⟩
  · intro j p w next total
    have bounded : total≤roof := room next
    refine ⟨actual_raw_scope_cuts_keep_the_fixed_ancestor_half_jets R F chart E B0 own tails legal
      shared pageBound fixed addr seed owner pageFit sizes bootFit owners p w (carry next)
      (exactAncestorJetWidth R F chart E B0 own next) (observed next) (jets next).2,?_,?_⟩
    · intro stop zero
      exact same_raw_zero_stop_has_all_named_clock_cuts X M basePos ord ownerInputs F chart tails B0 live
        valid p w stop zero total roof bounded
    · intro stop positive
      exact same_raw_positive_stop_has_all_named_clock_cuts X M basePos ord ownerInputs gate boot
        F E chart tails B0 own live valid supply gateWidth p w stop positive total roof bounded

#print axioms paper6_actual_raw_exterior_selected_phase_peak
end
end J6R75RawPeak
