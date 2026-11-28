import J6R68CanonicalRootWriterRateReadActual
import J6R68CanonicalRootWriterLiveRun

/-! The native exterior actually taking its root stop has the original
value and a size-based bound on its *own* execution Meter. Nothing in
this cap is an assumed bound for the leaf program, owner gather, book
traversal, or packet reader. Four upstream producer fees are visible. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6ActiveRun J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R67CanonicalStop J6R11Blueprint J6R49Leaf J6R51Leaf J6R34ChildPath
open J6R24MeteredRecursion J6R51Online J1PPrinted J6R10Reachable J6R30ProducedGateRegistry
open J6R64Active J6R66Active J6R54ExteriorOwner J6R50SourceProducer J6R50Leaf J6R52Terminal
open J6R53OldOwnerRoot J6R58BootScope J6R48Leaf

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 5300
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own old : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "E" => (exteriorChild G ell X.centre X.sample X.group).edges
local notation "U" => ((exteriorChild G ell X.centre X.sample X.group).host.Row ⊕
  (exteriorChild G ell X.centre X.sample X.group).host.Col)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)
variable (A : RootStopInputs X gate pad own old)

def paidRootUpstream : ℕ :=
  A.incident.emitted.steps+A.lanes.run.steps+A.keys.headers.steps+A.keys.dest.steps

def rootNativePreparationBound (B : Bank) (D : ℕ) : ℕ :=
  rootBookAfterInputs m own key prec Pg E+
    bootMountGeometry old own (SuffixWordWidth m) key prec Pg A.source.order.length
      (stagePageOrder X).length B.records.length (max D 2)+
    (3+Nat.card U*rootOwnerRowCap (SuffixWordWidth m) (rootHalfWidth m)
      own key prec Pg E (rootBodyWidth m) A.codeWidth (max D 2))+
    (4*E+2)+13

def actualStoppedRootBound (B : Bank) (F : Frame f (Ext).prec) (D : ℕ) : ℕ :=
  paidRootUpstream X gate pad A+rootNativePreparationBound X gate pad A B D+
    rawLeafCap F.words.length ell (Ext).prec E (Nat.card U)
      (Nat.card U*physicalRootReadCap X pad B F.words.length (Ext).prec A.codeWidth D) F.hp

theorem actual_paid_root_stop_has_explicit_uniform_size_bound
    (basePos : 0<base) (nameInj : Function.Injective A.localName)
    (srcInj : Function.Injective A.sourceName) (gateWidth : gate.created.val=base)
    (edgeCount : (Ext).host.edgeCount=E) (hb : 0<A.codeWidth) (fit : E ≤ 2^A.codeWidth)
    (F : Frame f (Ext).prec) (B : Bank) (live : IsLive (X.seed pad) B)
    (D : ℕ) (degree : ∀ u,plant.degree u ≤ D) :
    (meteredRootStop X gate pad A F B).steps ≤ actualStoppedRootBound X gate pad A B F D := by
  let setup := prepareRootBook X gate pad A.localName A.incident A.lanes
  let owners := mountFirstOwners X gate pad A.source B live A.keys srcInj
  let fs := trueFrames X gate pad A.localName
  let bk := frameKeys fs
  let cmds := owners.result.order.map (expectedRootCommand X pad edgeCount A.codeWidth fit)
  let eval := runRows X.hf F X.positive B (visitFramesClock fs).result cmds
  obtain ⟨ans,paid,_⟩ := metered_root_stop_uses_each_actual_producer_once X gate pad A basePos
    nameInj srcInj gateWidth edgeCount hb fit F B live
  have fee : (meteredRootStop X gate pad A F B).steps=
      setup.steps+owners.steps+
        (3+(owners.result.raw.map (fun u=>(writeRootOwner A.codeWidth bk.result fs u).steps+7)).sum)+
        (4*E+2)+eval.steps+13 := congrArg Meter.steps paid
  have boot := physical_root_book_fee_from_word_widths X gate pad A.localName A.incident A.lanes edgeCount
  have mount := actual_live_boot_mount_ceiling X gate pad A.source A.keys B live srcInj D degree
  have rows := physical_root_command_sum_from_edge_and_vertex_counts X gate pad A.localName
    owners.result edgeCount A.codeWidth D degree
  have e := same_root_interpreter_cutoff_fee_from_actual_dimensions X gate pad B live A.localName
    owners.result edgeCount F A.codeWidth D degree fit
  let book := rootBookAfterInputs m own key prec Pg E
  let raw := bootMountGeometry old own (SuffixWordWidth m) key prec Pg A.source.order.length
    (stagePageOrder X).length B.records.length (max D 2)
  let charges := Nat.card U*rootOwnerRowCap (SuffixWordWidth m) (rootHalfWidth m) own key prec Pg E
    (rootBodyWidth m) A.codeWidth (max D 2)
  let reading := rawLeafCap F.words.length ell (Ext).prec E (Nat.card U)
    (Nat.card U*physicalRootReadCap X pad B F.words.length (Ext).prec A.codeWidth D) F.hp
  unfold actualStoppedRootBound paidRootUpstream rootNativePreparationBound
  change _ ≤ A.incident.emitted.steps+A.lanes.run.steps+A.keys.headers.steps+A.keys.dest.steps+
    (book+raw+(3+charges)+(4*E+2)+13)+reading
  rw [fee]
  change setup.steps ≤ A.incident.emitted.steps+A.lanes.run.steps+book at boot
  change owners.steps ≤ A.keys.headers.steps+A.keys.dest.steps+raw at mount
  change (owners.result.raw.map (fun u=>(writeRootOwner A.codeWidth bk.result fs u).steps+7)).sum ≤
    charges at rows
  change eval.steps ≤ reading at e
  omega

variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Here" => (Path.root : Path sel
  (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
local notation "Machine" => (OnlineMachine T key prec tw bw Pg rate)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

theorem same_original_stopped_run_root_writes_has_explicit_cap
    (M : Machine) (Rtn : RetainedAfter T key prec tw bw Pg rate cw)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    (retire : PageJob f ell key prec tw bw Pg→ℕ)
    (B : Bank) (head : OwnsHeader X.header.result B) (live : IsLive (X.seed pad) B)
    (stop : E ≤ (printedParams (f:=f) (ell:=ell) s).cutoff)
    (basePos : 0<base) (nameInj : Function.Injective A.localName)
    (srcInj : Function.Injective A.sourceName) (gateWidth : gate.created.val=base)
    (hb : 0<A.codeWidth) (fit : E ≤ 2^A.codeWidth)
    (D : ℕ) (degree : ∀ u,plant.degree u ≤ D) :
    let F := T.frame (Here).reached
    let actual := runPhysicalExterior X (withCanonicalRootWriter X gate pad A M) Rtn layout retire B head
    actual.result.2=B ∧ F.decode actual.result.1=(sourceBlueprint sel Ext X.hf).program.run Ext ∧
      actual.steps ≤ actualStoppedRootBound X gate pad A B F D := by
  let F := T.frame (Here).reached
  let E0 := planEdges (T:=T) Here
  have bound := actual_paid_root_stop_has_explicit_uniform_size_bound X gate pad A
    basePos nameInj srcInj gateWidth E0 hb fit F B live D degree
  obtain ⟨ans,paid,value⟩ := metered_root_stop_uses_each_actual_producer_once X gate pad A basePos
    nameInj srcInj gateWidth E0 hb fit F B live
  dsimp only
  rw [physical_root_stop_runs_exact_paid_provider X gate pad A M Rtn layout retire B head stop]
  refine ⟨rfl,?_ ,bound⟩
  change F.decode (meteredRootStop X gate pad A F B).result=_
  rw [paid]
  exact value.trans (true_source_stops_on_same_host T Here stop)

#print axioms actual_paid_root_stop_has_explicit_uniform_size_bound
#print axioms same_original_stopped_run_root_writes_has_explicit_cap
end
end J6R68CanonicalRootWriter
