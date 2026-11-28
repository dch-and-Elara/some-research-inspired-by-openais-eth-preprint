import J6R65LeafRateRootZero
import J6R62LeafActual

/-! Apply the printed cutoff to the same positive mounted leaf as R62.
The supplier's acquisition is paid once and does not multiply by
the assignment count. Real command fees remain on the reached bank. -/
namespace J6R65LeafRate
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins
open J6R26DescriptorTree J6R34ChildPath J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R9Recursive J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf J6R48DFS
open J6R57Public J6R58LeafScale J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R37StructuredRoot J6R41StructuredAllPaths

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 42000000
set_option maxRecDepth 5000

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
local notation "H" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))

variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

section Parts
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))

def positiveSetup (A : OwnerTerminalInput X p w Y) : ℕ :=
  let U := observedFrameWidth A.saved.rows
  let d := observedGateWidth A.roster.raw
  ownerCensusFee X p w Y U d+atlasCensusFee X p w Y U+
    (4*Nat.card (p.ticket w).child.host.Row+3)+(4*(p.ticket w).child.edges+2)+18

def positiveReadBill (older : List Cmd) (B : Bank) : ℕ :=
  let ch := (p.ticket w).child
  cmdBill B (4*Nat.clog 2 s) ch.prec ch.edges (older++(trueFreshPages Y).map (freshWord Y))
end Parts

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)

include boot in
theorem actual_positive_readLeaf_with_printed_factor
    (B : Bank) (rootLive : IsLive (X.seed pad) B) (valid : ReadyOnStack (borns M) B)
    (supply : HasMeasuredOwnerInputs X M ownerInputs) (gateWidth : gate.created.val=base)
    (stop : ((Plan sel).child c w).edges≤(SP).cutoff) (positive : 0<((Plan sel).child c w).edges) :
    let Y := sourceState M p w
    let walk := Path.step p w
    let native := stackBank (borns M) B walk
    let leaf := readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) B walk stop
    let F := T.frame walk.reached
    ∃ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
      (ownerInputs p w Y stop).result=some A ∧
      (oldCompiler X p w Y A).result=some older ∧
      F.decode leaf.result=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) ∧
      leaf.steps≤finiteStopFee (ownerInputs p w Y stop).steps (positiveSetup X p w Y A)
        (positiveReadBill X p w Y older native) (sourceArithmetic s C (ext)) H := by
  let Y := sourceState M p w
  let walk := Path.step p w
  let native := stackBank (borns M) B walk
  let leaf := readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) B walk stop
  let F := T.frame walk.reached
  let ch := (p.ticket w).child
  obtain ⟨A,older,supplied,compiled,value,fee⟩ :=
    mounted_positive_leaf_is_exact_and_has_source_sized_fee X p w M basePos ord ownerInputs
      gate boot B stop positive gateWidth rootLive valid supply
  let bill := positiveReadBill X p w Y older native
  let ar := sourceArithmetic s C (ext)
  let baseFee := (ownerInputs p w Y stop).steps
  let extra := positiveSetup X p w Y A
  have dims := actual_leaf_field_width_and_vertices (T:=T) walk
  have pf : ch.prec≤(ext).prec+160*C*s^2 := dims.2.1
  have vf : vertexCount ch.host≤vertexCount (ext).host+4*(C*s) := dims.2.2
  let raw := rawLeafCap (4*Nat.clog 2 s) ell ch.prec ch.edges (vertexCount ch.host) bill F.hp
  have arcap : raw≤2^H*(bill+ar) :=
    raw_leaf_fee_from_dimensions F.hp le_rfl le_rfl pf stop vf
  have splitFee : leaf.steps≤baseFee+extra+raw := by
    change leaf.steps≤baseFee+
      ownerCensusFee X p w Y (observedFrameWidth A.saved.rows) (observedGateWidth A.roster.raw)+
      atlasCensusFee X p w Y (observedFrameWidth A.saved.rows)+
      (4*Nat.card ch.host.Row+3)+(4*ch.edges+2)+raw+15+3 at fee
    change leaf.steps≤baseFee+(ownerCensusFee X p w Y (observedFrameWidth A.saved.rows)
      (observedGateWidth A.roster.raw)+atlasCensusFee X p w Y (observedFrameWidth A.saved.rows)+
      (4*Nat.card ch.host.Row+3)+(4*ch.edges+2)+18)+raw
    omega
  exact ⟨A,older,supplied,compiled,value,splitFee.trans (Nat.add_le_add_left arcap _)⟩

#print axioms positiveSetup
#print axioms positiveReadBill
#print axioms actual_positive_readLeaf_with_printed_factor
end
end J6R65LeafRate
