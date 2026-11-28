import J6R67UnifiedRateLeaf
import J6R67UnifiedRateScope
import J6R67UnifiedRateActive

/-! Final actual Phase attachment: R65 measured leaves, R64/R66 finite
active words, and R57 primitive scope envelopes, on the same physical
exterior call and actual resident bank. -/
namespace J6R67UnifiedRate
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
open J6R63Active J6R57ActiveFee J6R57ScopeFee J6R51Peak

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
variable {pad s C rate cw : ℕ} {cfg : RootBounds s C f}
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

theorem actual_marked_exterior_read_fits_words
    (B : Bank) (own : OwnsHeader X.header.result B)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    (K : ℕ) (precFit : prec≤K) (edgeFit : edgew≤K)
    (addrFit : externalAddrWidth tc tj 0≤K) (one : 1≤K) :
    ((physicalExteriorInputs X layout).inherit B own).steps≤20*K+13 := by
  change (readExterior X B own).steps≤_
  rw [(paid_actual_exterior_entry X B own).2.2]
  unfold callReadFee headerReadFee
  omega

def actualNonleafNodeFixed (K mask baseFee layoutFee : ℕ) : ℕ :=
  activeNodeFixedPrice K (liveActiveTapeRoof K) mask (baseFee+layoutFee+sharedHeaderAndCopyRoof K)

def combinedActualFixed (provider prep reader leafPower K mask baseFee layoutFee : ℕ) : ℕ :=
  max (combinedLeafBound (s:=s) (C:=C) X provider prep reader leafPower)
    (actualNonleafNodeFixed K mask baseFee layoutFee)

theorem header_fits_from_the_same_scope_widths
    (B : Bank) (scopeInputs : MeasuredScopeInputs R B) (K seed : ℕ)
    (mount : ActualMountWidths R K seed) (copyW : cw≤K) (edgeW : edgew≤K)
    (fixed : scopeInputs.wordCaps.fixed≤K) :
    LiveHeaderFits R cw edgew K := by
  refine ⟨mount.precisionWord,copyW,edgeW,?_⟩
  intro c p w
  let Y := sourceState R p w
  have observed := ((scopeInputs.fit.entry p w).1).trans fixed
  change fixedWords Y.birth≤K at observed
  unfold fixedWords at observed
  have off : Y.birth.job.offset=Y.birth.tc+(Y.birth.tz+(Y.birth.tm+6)) := rfl
  change Y.birth.edge≤K ∧ Y.birth.dep≤K ∧ Y.birth.job.offset≤K
  omega

include boot in
theorem same_physical_run_rate_from_native_dimensions_and_measured_primitives
    (B : Bank) (rootLive : IsLive (X.seed pad) B) (own : OwnsHeader X.header.result B)
    (valid : ReadyOnStack (borns M) B) (supply : HasMeasuredOwnerInputs X M ownerInputs)
    (gateWidth : gate.created.val=base)
    (F : RetainedAfter T key prec tw bw Pg rate cw)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    {pointerWidth : ℕ} (tails : SavedDirectoryTails pointerWidth)
    (scopeInputs : MeasuredScopeInputs R B)
    (provider prep reader leafPower K seed baseFee layoutFee mask scale localPower : ℕ)
    (parts : MeasuredStopParts X M basePos ord ownerInputs B provider prep reader leafPower)
    (copyWidth : cw≤K) (outerEdgeWidth : edgew≤K)
    (scopeFixedWidth : scopeInputs.wordCaps.fixed≤K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=rate) (r:=Ext) K)
    (cs : PrintedCentreScale s C K) (mount : ActualMountWidths R K seed)
    (offset : externalAddrWidth tc tj 0≤K)
    (baseDebit : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      (preparedActive R z.2 a).steps≤baseFee)
    (retainedDebit : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      currentLayoutDebit R F (physicalExteriorInputs X layout) B own z.2 a≤layoutFee)
    (high : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      z.1.prec+(preparedActive R z.2 a).result.extraPrecision≤K)
    (masks : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges) t u,
      (((preparedActive R z.2 a).result.tape t).masks u).steps≤mask)
    (fit : (Ext).depth≤pathLimit s C) {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (anchorPrec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor Ext)
    (numeric : combinedActualFixed (s:=s) (C:=C) X provider prep reader leafPower K mask baseFee layoutFee+
      (physicalAddressUnit K+measuredPerScope scopeInputs pointerWidth)≤scale*2^(localPower*LeafH)) :
    let out := runPhysicalExterior X R F layout (retireSavedDirectory tails) B own
    (T.frame (Here).reached).decode out.result.1=
      reduce (Ext).prec f ell ((Ext).host.contract X.hf) ∧ out.result.2=B ∧
    out.steps≤(pathLimit s C-(Ext).depth+1)*scale*2^((fullPrefixConstant C+localPower)*LeafH) := by
  let fixed := combinedActualFixed (s:=s) (C:=C) X provider prep reader leafPower K mask baseFee layoutFee
  let perScope := measuredPerScope scopeInputs pointerWidth
  have leafFits : combinedLeafBound (s:=s) (C:=C) X provider prep reader leafPower≤fixed :=
    le_max_left _ _
  have activeFits : actualNonleafNodeFixed K mask baseFee layoutFee≤fixed := le_max_right _ _
  have width := header_fits_from_the_same_scope_widths X M basePos ord ownerInputs B scopeInputs K seed
    mount copyWidth outerEdgeWidth scopeFixedWidth
  have one : 1≤K := (Nat.succ_le_of_lt M.modeWidth).trans ws.modeWord
  have rootRead := actual_marked_exterior_read_fits_words X B own layout K width.precFit width.extEdge offset one
  apply same_physical_run_with_three_measured_leaf_branches X M basePos ord ownerInputs gate boot
    B rootLive own valid supply gateWidth F layout (retireSavedDirectory tails)
    provider prep reader leafPower fixed (physicalAddressUnit K) perScope scale localPower parts leafFits
    _ _ fit stable zero anchorPrec link numeric
  · intro z a
    have localFee := actual_active_affine_from_paid_dimensions R F (physicalExteriorInputs X layout) B own z.2 a
      K seed baseFee layoutFee mask width ws cs mount rootRead (baseDebit z a)
      (retainedDebit z a) (high z a) (masks z a)
    exact localFee.trans (Nat.add_le_add_right activeFits _)
  · intro z w
    exact live_scope_has_derived_fee scopeInputs tails z.2 w

#print axioms actual_marked_exterior_read_fits_words
#print axioms header_fits_from_the_same_scope_widths
#print axioms same_physical_run_rate_from_native_dimensions_and_measured_primitives
end
end J6R67UnifiedRate

