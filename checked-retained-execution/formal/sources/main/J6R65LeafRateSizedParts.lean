import J6R65LeafRateCombine
import J6R65LeafRatePrepGeometry

/-! Derive the prep portion of the all-stop R56 contract from word
and frame widths on the real source. Only actual directory/entry
tariffs and measured input acquisition still need separate caps. -/
namespace J6R65LeafRate
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 43000000
set_option maxRecDepth 4900

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
local notation "Bank65" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)

def sourcePreparationLimit (s C pad W own U Uzero d : ℕ) : ℕ :=
  printedPreparation (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
    (vertexCount (ext).host+4*(C*s)) (3*(C*s)) W own key prec
    (pageKeyWidth m+pad) (pageKeyWidth m+J6Mesh.a m) U d+
  zeroPreparation (C*s) W Uzero

theorem true_widths_supply_all_source_preparation
    (initialBank : Bank65) (provider reader K W own U Uzero d : ℕ)
    (rootRead : (ext).edges≤(SP).cutoff → rootLiteralBill X M basePos ord initialBank≤reader*2^(K*LeafH))
    (zeroRead : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c),
      ((Plan sel).child c w).edges=0 → zeroLiteralBill X M basePos p w initialBank≤reader*2^(K*LeafH))
    (paid : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c)
      (stop : ((Plan sel).child c w).edges≤(SP).cutoff),
      0<((Plan sel).child c w).edges → (ownerInputs p w (sourceState M p w) stop).steps≤provider)
    (zeroWidths : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c),
      ((Plan sel).child c w).edges=0 →
      let Y := sourceState M p w
      Y.birth.port≤W ∧ observedBookBodyWidth p w Y≤Uzero)
    (positiveWidths : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c)
      (stop : ((Plan sel).child c w).edges≤(SP).cutoff),
      0<((Plan sel).child c w).edges →
      let Y := sourceState M p w
      ∀ (A : OwnerTerminalInput X p w Y), (ownerInputs p w Y stop).result=some A →
        Y.birth.port≤W ∧ Y.site.ownerWidth≤own ∧ observedFrameWidth A.saved.rows≤U ∧
        observedGateWidth A.roster.raw≤d)
    (positiveRead : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c)
      (stop : ((Plan sel).child c w).edges≤(SP).cutoff),
      0<((Plan sel).child c w).edges →
      let Y := sourceState M p w
      let B := stackBank (borns M) initialBank (Path.step p w)
      ∀ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
        (ownerInputs p w Y stop).result=some A → (oldCompiler X p w Y A).result=some older →
        positiveReadBill X p w Y older B≤reader*2^(K*LeafH)) :
    MeasuredStopParts X M basePos ord ownerInputs initialBank provider
      (sourcePreparationLimit X s C pad W own U Uzero d) reader K := by
  unfold MeasuredStopParts
  refine ⟨rootRead,?_,paid,?_⟩
  · intro c p w hzero
    obtain ⟨wp,body⟩ := zeroWidths p w hzero
    have bp := true_zero_preparation_from_chart_widths X p w (sourceState M p w) wp body
    exact ⟨bp.trans (Nat.le_add_left _ _),zeroRead p w hzero⟩
  · intro c p w stop positive
    dsimp only
    intro A older hit old
    obtain ⟨port,ow,bod,arity⟩ := positiveWidths p w stop positive A hit
    have bp := true_positive_preparation_from_chart_dimensions X p w (sourceState M p w) A stop
      port ow bod arity
    exact ⟨bp.trans (Nat.le_add_right _ _),positiveRead p w stop positive A older hit old⟩

#print axioms sourcePreparationLimit
#print axioms true_widths_supply_all_source_preparation
end
end J6R65LeafRate
