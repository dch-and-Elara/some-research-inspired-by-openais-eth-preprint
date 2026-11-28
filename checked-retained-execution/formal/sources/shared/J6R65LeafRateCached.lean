import J6R65LeafRateCombine

/-! Apply the stopped branch estimate to the actual cached occurrence
ledger, retaining the measured nonleaf phases and final numerical
envelope explicitly. No arbitrary LeafAgreement or leaf cap is passed. -/
namespace J6R65LeafRate
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable J6R52CacheWhole
open J6R54PeakInput

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 43000000
set_option maxRecDepth 5500

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "LeafH" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local instance exactDecision :
  DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
    (exteriorChild G ell X.centre X.sample X.group)) :=
  J6R24MeteredRecursion.sourceDecision sel (ext)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)

include boot in
theorem same_R56_cached_run_after_replacing_whole_leaf_cap
    (initialBank : Bank)
    (rootLive : IsLive (X.seed pad) initialBank) (valid : ReadyOnStack (borns M) initialBank)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
    (provider preparation reader K arithmetic perScope scale localPower : ℕ)
    (parts : MeasuredStopParts X M basePos ord ownerInputs initialBank provider preparation reader K)
    (active : ∀ (z : Sigma (Path sel ext)) (a : (SP).cutoff<z.1.edges),
      let R := withPaidOwnerLeaves X M basePos ord ownerInputs
      let A := preparedActive R z.2 a
      cacheMountFee R z.2+A.steps+streamActiveTariff A.result
        (reachable_positive T z.2.reached) T.vPositive≤
          combinedLeafBound (s:=s) (C:=C) X provider preparation reader K+
            arithmetic*Nat.card ((Plan sel).Slot z.1))
    (scope : ∀ (z : Sigma (Path sel ext)) (w : (Plan sel).Slot z.1),
      cachedScopeOwn (withPaidOwnerLeaves X M basePos ord ownerInputs) retire initialBank z.2 w≤perScope)
    (fit : (ext).depth≤pathLimit s C)
    {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (anchorPrec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor (ext))
    (numeric : combinedLeafBound (s:=s) (C:=C) X provider preparation reader K+(arithmetic+perScope)
      ≤scale*2^(localPower*LeafH)) :
    let R := withPaidOwnerLeaves X M basePos ord ownerInputs
    let out := runCachedRootSingleEmission R retire initialBank
    (T.frame (Path.root : Path sel ext ext).reached).decode out.result.1=
      reduce (ext).prec f ell ((ext).host.contract X.hf) ∧ out.result.2=initialBank ∧
      out.steps≤(pathLimit s C-(ext).depth+1)*scale*2^((fullPrefixConstant C+localPower)*LeafH) := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  have eq : ReadyOnStack (borns M) initialBank=ReadyOnStack (borns R) initialBank :=
    congrArg (fun birth : Births T key prec tw bw (pageKeyWidth m+pad)=>ReadyOnStack birth initialBank)
      (paid_owner_leaf_keeps_births X M basePos ord ownerInputs).symm
  have stayed : ReadyOnStack (borns R) initialBank :=
    @Eq.mp (ReadyOnStack (borns M) initialBank) (ReadyOnStack (borns R) initialBank)
      eq (fun {_} p w=>valid p w)
  have leaves : LeafAgreement R initialBank := same_source_terminal_agrees_without_LoopCharts
    X M basePos ord ownerInputs gate boot initialBank gateWidth rootLive valid supply
  have phases := actual_R56_caps_from_measured_leaf_parts X M basePos ord ownerInputs gate boot initialBank
    rootLive valid supply gateWidth retire provider preparation reader K arithmetic perScope parts active scope
  exact actual_cached_physical_output_and_compressed_rate_under_three_phase_caps R retire initialBank stayed
    leaves fit stable zero anchorPrec link _ arithmetic perScope scale localPower phases numeric

#print axioms same_R56_cached_run_after_replacing_whole_leaf_cap
end
end J6R65LeafRate
