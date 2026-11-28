import J6R65LeafRatePositive
import J6R56PrintedExponentPhases

/-! One bound for exactly the three source stopping branches. The
numeric assumptions refer to real roster/atlas preparation, actual
bank-reader tariffs, and the paid provider; none is a cap on readLeaf.
The result implements the real R56 leaf field. -/
namespace J6R65LeafRate
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins
open J6R26DescriptorTree J6R34ChildPath J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf J6R48DFS
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R37StructuredRoot J6R41StructuredAllPaths J6R55CachedLedger J6R56PrintedExponent
open J6R49Cost J6R16ModeCost J6R10Reachable

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 43000000
set_option maxRecDepth 5100

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
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
def MeasuredStopParts (initialBank : Bank) (provider preparation reader K : ℕ) : Prop :=
  ((ext).edges≤(SP).cutoff → rootLiteralBill X M basePos ord initialBank≤reader*2^(K*LeafH)) ∧
  (∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c),
      ((Plan sel).child c w).edges=0 →
      zeroBookSetup p w (sourceState M p w)≤preparation ∧
      zeroLiteralBill X M basePos p w initialBank≤reader*2^(K*LeafH)) ∧
  (∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c)
      (stop : ((Plan sel).child c w).edges≤(SP).cutoff),
      0<((Plan sel).child c w).edges → (ownerInputs p w (sourceState M p w) stop).steps≤provider) ∧
  (∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c)
      (stop : ((Plan sel).child c w).edges≤(SP).cutoff),
      0<((Plan sel).child c w).edges →
      let Y := sourceState M p w
      let native := stackBank (borns M) initialBank (Path.step p w)
      ∀ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
        (ownerInputs p w Y stop).result=some A →
        (oldCompiler X p w Y A).result=some older →
        positiveSetup X p w Y A≤preparation ∧
        positiveReadBill X p w Y older native≤reader*2^(K*LeafH))

def combinedLeafBound (provider preparation reader K : ℕ) : ℕ :=
  provider+(preparation+reader+sourceArithmetic s C (ext))*2^((K+1)*LeafH)

variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)

include boot in
theorem all_stopped_readLeaf_has_combined_source_cap
    (initialBank : Bank)
    (rootLive : IsLive (X.seed pad) initialBank) (valid : ReadyOnStack (borns M) initialBank)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (provider preparation reader K : ℕ)
    (parts : MeasuredStopParts X M basePos ord ownerInputs initialBank provider preparation reader K)
    (z : Sigma (Path sel ext)) (stop : z.1.edges≤(SP).cutoff) :
    (readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) initialBank z.2 stop).steps≤
      combinedLeafBound (s:=s) (C:=C) X provider preparation reader K := by
  let ar := sourceArithmetic s C (ext)
  unfold MeasuredStopParts at parts
  obtain ⟨rootCap,zeroCap,payCap,posCap⟩ := parts
  obtain ⟨_,path⟩ := z
  cases path with
  | root =>
    have fee := actual_root_run_has_printed_leaf_factor X M basePos ord ownerInputs initialBank rootLive stop
    have m := structural_leaf_fee_into_printed_rate (provider:=0) (setup:=0)
      (bill:=rootLiteralBill X M basePos ord initialBank) (arithmetic:=ar) (H:=LeafH)
      (Bprep:=preparation) (Bread:=reader) (K:=K) (Nat.zero_le _) (rootCap stop)
    simp only [finiteStopFee,Nat.zero_add] at m
    exact (fee.trans m).trans (Nat.le_add_left _ _)
  | step p w =>
    by_cases zero : ((Plan sel).child _ w).edges=0
    · have fee := actual_zero_leaf_pays_true_book_and_one_assignment X M basePos ord ownerInputs
        p w initialBank rootLive valid stop zero
      obtain ⟨ps,rb⟩ := zeroCap p w zero
      let setup := zeroBookSetup p w (sourceState M p w)
      let bill := zeroLiteralBill X M basePos p w initialBank
      have basic : setup+bill+ar≤finiteStopFee 0 setup bill ar LeafH := by
        unfold finiteStopFee
        simp only [Nat.zero_add,Nat.add_assoc]
        exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by positivity)) _
      have m := structural_leaf_fee_into_printed_rate (provider:=0) (setup:=setup) (bill:=bill)
        (arithmetic:=ar) (H:=LeafH) ps rb
      simp only [Nat.zero_add] at m
      exact ((fee.trans basic).trans m).trans (Nat.le_add_left _ _)
    · have positive := Nat.pos_of_ne_zero zero
      obtain ⟨A,older,acquired,compiled,_,fee⟩ :=
        actual_positive_readLeaf_with_printed_factor X p w M basePos ord ownerInputs
          gate boot initialBank rootLive valid supply gateWidth stop positive
      obtain ⟨ps,rb⟩ := posCap p w stop positive A older acquired compiled
      have pay := payCap p w stop positive
      have m := structural_leaf_fee_into_printed_rate (arithmetic:=ar) (H:=LeafH)
        (provider:=(ownerInputs p w (sourceState M p w) stop).steps) ps rb
      exact (fee.trans m).trans (Nat.add_le_add_right pay _)

include boot in
theorem actual_R56_caps_from_measured_leaf_parts
    (initialBank : Bank)
    (rootLive : IsLive (X.seed pad) initialBank) (valid : ReadyOnStack (borns M) initialBank)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
    (provider preparation reader K arithmetic perScope : ℕ)
    (parts : MeasuredStopParts X M basePos ord ownerInputs initialBank provider preparation reader K)
    (active : ∀ (z : Sigma (Path sel ext)) (a : (SP).cutoff<z.1.edges),
      let R := withPaidOwnerLeaves X M basePos ord ownerInputs
      let A := preparedActive R z.2 a
      cacheMountFee R z.2+A.steps+streamActiveTariff A.result
        (reachable_positive T z.2.reached) T.vPositive≤
        combinedLeafBound (s:=s) (C:=C) X provider preparation reader K+
          arithmetic*Nat.card ((Plan sel).Slot z.1))
    (scope : ∀ (z : Sigma (Path sel ext)) (w : (Plan sel).Slot z.1),
      cachedScopeOwn (withPaidOwnerLeaves X M basePos ord ownerInputs) retire initialBank z.2 w≤perScope) :
    CachedThreePhaseCaps (withPaidOwnerLeaves X M basePos ord ownerInputs) retire initialBank
      (combinedLeafBound (s:=s) (C:=C) X provider preparation reader K) arithmetic perScope :=
  ⟨all_stopped_readLeaf_has_combined_source_cap X M basePos ord ownerInputs gate boot initialBank rootLive
    valid supply gateWidth provider preparation reader K parts,active,scope⟩

#print axioms MeasuredStopParts
#print axioms all_stopped_readLeaf_has_combined_source_cap
#print axioms actual_R56_caps_from_measured_leaf_parts
end
end J6R65LeafRate
