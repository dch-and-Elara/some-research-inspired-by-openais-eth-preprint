import J6R66ActivePhase
import J6R66ActiveExterior
import J6R65LeafRateCached

/-! The actual R66 physical runner with exactly the R65 three
stopping branches. No leaf interpreter, root selection, or zero
tape is constructed here. The two results use the same StableExterior,
same already-live bank, and same selected executable paths. -/
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
local instance exactDecision :
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

theorem replacing_leaves_preserves_actual_ready_stack
    (B : Bank) (valid : ReadyOnStack (borns M) B) :
    ReadyOnStack (borns R) B := by
  have same : ReadyOnStack (borns M) B=ReadyOnStack (borns R) B :=
    congrArg (fun births : Births T key prec tw bw Pg=>ReadyOnStack births B)
      (paid_owner_leaf_keeps_births X M basePos ord ownerInputs).symm
  exact @Eq.mp (ReadyOnStack (borns M) B) (ReadyOnStack (borns R) B)
    same (fun {_} p w=>valid p w)

include boot in
theorem actual_leaf_caps_on_the_r66_physical_run
    (B : Bank) (rootLive : IsLive (X.seed pad) B) (own : OwnsHeader X.header.result B)
    (valid : ReadyOnStack (borns M) B) (supply : HasMeasuredOwnerInputs X M ownerInputs)
    (gateWidth : gate.created.val=base)
    (F : RetainedAfter T key prec tw bw Pg rate cw)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    (retire : Job→ℕ)
    (provider preparation reader K fixed arithmetic perScope : ℕ)
    (parts : MeasuredStopParts X M basePos ord ownerInputs B provider preparation reader K)
    (leafFits : combinedLeafBound (s:=s) (C:=C) X provider preparation reader K ≤ fixed)
    (active : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      let A := liveActiveAt R F (physicalExteriorInputs X layout) B own z.2 a
      cacheMountFee R z.2+A.steps+streamActiveTariff A.result
        (reachable_positive T z.2.reached) T.vPositive ≤
        fixed+arithmetic*Nat.card ((Plan sel).Slot z.1))
    (scope : ∀ (z : Sigma (Path sel Ext)) (w : (Plan sel).Slot z.1),
      cachedScopeOwn R retire B z.2 w ≤ perScope) :
    LiveCaps R F (physicalExteriorInputs X layout) retire B own fixed arithmetic perScope := by
  refine ⟨?_,active,scope⟩
  intro z stop
  exact (all_stopped_readLeaf_has_combined_source_cap X M basePos ord ownerInputs gate boot B
    rootLive valid supply gateWidth provider preparation reader K parts z stop).trans leafFits

include boot in
theorem same_physical_run_with_three_measured_leaf_branches
    (B : Bank) (rootLive : IsLive (X.seed pad) B) (own : OwnsHeader X.header.result B)
    (valid : ReadyOnStack (borns M) B) (supply : HasMeasuredOwnerInputs X M ownerInputs)
    (gateWidth : gate.created.val=base)
    (F : RetainedAfter T key prec tw bw Pg rate cw)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    (retire : Job→ℕ)
    (provider preparation reader K fixed arithmetic perScope scale localPower : ℕ)
    (parts : MeasuredStopParts X M basePos ord ownerInputs B provider preparation reader K)
    (leafFits : combinedLeafBound (s:=s) (C:=C) X provider preparation reader K ≤ fixed)
    (active : ∀ (z : Sigma (Path sel Ext)) (a : (SP).cutoff<z.1.edges),
      let A := liveActiveAt R F (physicalExteriorInputs X layout) B own z.2 a
      cacheMountFee R z.2+A.steps+streamActiveTariff A.result
        (reachable_positive T z.2.reached) T.vPositive ≤
        fixed+arithmetic*Nat.card ((Plan sel).Slot z.1))
    (scope : ∀ (z : Sigma (Path sel Ext)) (w : (Plan sel).Slot z.1),
      cachedScopeOwn R retire B z.2 w ≤ perScope)
    (fit : (Ext).depth≤pathLimit s C) {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (anchorPrec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor Ext)
    (numeric : fixed+(arithmetic+perScope)≤scale*2^(localPower*LeafH)) :
    let out := runPhysicalExterior X R F layout retire B own
    (T.frame (Here).reached).decode out.result.1=
      reduce (Ext).prec f ell ((Ext).host.contract X.hf) ∧ out.result.2=B ∧
    out.steps≤(pathLimit s C-(Ext).depth+1)*scale*2^((fullPrefixConstant C+localPower)*LeafH) := by
  have stayed : ReadyOnStack (borns R) B :=
    replacing_leaves_preserves_actual_ready_stack X M basePos ord ownerInputs B valid
  have leaves : LeafAgreement R B :=
    same_source_terminal_agrees_without_LoopCharts X M basePos ord ownerInputs gate boot
      B gateWidth rootLive valid supply
  have caps := actual_leaf_caps_on_the_r66_physical_run X M basePos ord ownerInputs gate boot
    B rootLive own valid supply gateWidth F layout retire provider preparation reader K
    fixed arithmetic perScope parts leafFits active scope
  exact same_actual_run_output_and_rate_under_live_phase_caps R F (physicalExteriorInputs X layout)
    retire B own stayed leaves fit stable zero anchorPrec link fixed arithmetic perScope
    scale localPower caps numeric

#print axioms replacing_leaves_preserves_actual_ready_stack
#print axioms actual_leaf_caps_on_the_r66_physical_run
#print axioms same_physical_run_with_three_measured_leaf_branches
end
end J6R67UnifiedRate

