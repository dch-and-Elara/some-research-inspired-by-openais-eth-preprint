import J6R102FinalPhaseUniform
import J6R68ActiveInputsSweepPhysical

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
local notation "R" => (withPaidOwnerLeaves X M basePos ord ownerInputs)

theorem phases_on_the_exact_raw_runner
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
      (C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1)) ≤ K) :
    let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X :=
      fun b h a=>(D.exterior b h a).run
    let E := physicalExteriorInputs X layout
    let Q := proofDrivers R (D.retained fitActive) chart E B own
    let fixed := max (combinedLeafBound (s:=s) (C:=C) X provider prep reader leafPower)
      (sweptActivePx K (ingressFee+selectedLayoutRoof K+3))
    CachedThreePhaseCaps Q (retireSavedDirectory tails) B fixed
      (physicalAddressUnit K) (measuredPerScope scopeInputs pointerWidth) := by
  let layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=rank+1) X :=
    fun b h a=>(D.exterior b h a).run
  let F := D.retained fitActive
  let E := physicalExteriorInputs X layout
  let Q := proofDrivers R F chart E B own
  let budget := ingressFee+selectedLayoutRoof K+3
  let fixed := max (combinedLeafBound (s:=s) (C:=C) X provider prep reader leafPower) (sweptActivePx K budget)
  let perScope := measuredPerScope scopeInputs pointerWidth
  let tariff : Job → ℕ := retireSavedDirectory tails
  have actualFee (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges) :
      currentLayoutDebit R F E B own z.2 a ≤ budget := by
    change currentLayoutDebit R (D.retained fitActive) (D.rootInputs (readExterior X)) B own z.2 a ≤ _
    rw [actual_current_debit_is_the_paid_greedy_step D R B own (readExterior X) fitActive z.2 a]
    exact chosen_setup_uniform (D.atPath R B own z.2 a) K ingressFee (targetShape z a) (rawDebit z a)
  have width := header_fits_from_the_same_scope_widths X M basePos ord ownerInputs B scopeInputs K seed
    mount copyWidth outerEdgeWidth scopeFixedWidth
  have one : 1 ≤ K := (Nat.succ_le_of_lt M.modeWidth).trans ws.modeWord
  have rootRead := actual_marked_exterior_read_fits_words X B own layout K width.precFit width.extEdge offset one
  change CachedThreePhaseCaps Q tariff B fixed (physicalAddressUnit K) perScope
  refine ⟨?_,?_,?_⟩
  · intro z stop
    change (readLeaf (proofDrivers R F chart E B own) B z.2 stop).steps ≤ fixed
    rw [raw_view_leaf_reads_the_same_meter]
    exact (stopped z stop).trans (le_max_left _ _)
  · intro z a
    have derived := actual_raw_path_has_derived_active_fields R F chart E B own
      z.2 a K budget width ws cs rootRead (actualFee z a) absoluteHigh
    exact (actual_swept_active_bill_is_affine R F chart E B own z.2 a K seed budget ws cs mount derived).trans
      (Nat.add_le_add_right (le_max_right _ _) _)
  · intro z w
    change cachedScopeOwn (proofDrivers R F chart E B own) tariff B z.2 w ≤ perScope
    rw [raw_scope_keeps_original_own_fee]
    exact live_scope_has_derived_fee scopeInputs tails z.2 w

#print axioms phases_on_the_exact_raw_runner
end
end J6R102FinalPhase

