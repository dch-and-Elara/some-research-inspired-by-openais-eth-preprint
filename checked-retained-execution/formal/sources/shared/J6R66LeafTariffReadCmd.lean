import J6R66LeafTariffNative
import J6R66LeafTariffExterior
import J6R62LeafOldFormat

/-! Consume the previous results at the actual native terminal read
requests: the fresh row is the original `freshWord`, and the inherited
row uses the immutable job from the true ancestor trace. -/
namespace J6R66LeafTariff
open scoped Polynomial Classical
open AOracleMachineTime J6R21Ancestor J6R18ChildWrite J6R32ChildResidentTransfer J6R16ModeCost
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R34RootAtlas J6R32StatefulArithmetic
open J6R24MeteredRecursion J6R48Leaf J6R50Leaf J6R62Leaf J6R65LeafRate J6R51Online
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R26DescriptorTree J6R27OriginalGate J6R34ChildPath J6R51Leaf J6R52Terminal J6R50SourceProducer J6R54TerminalBoot
open J6Mesh J6OrientedHost J6R24LegalLayout J6R26StablePreparedRoot J6R35RootOrigins J6R31RootResidentTables

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 27000000
set_option maxRecDepth 4400
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "H" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))

theorem actual_fresh_command_has_printed_reader_rate
    (M : OnlineMachine T key prec tw bw page rate)
    (par : Path sel r c) (slot : (Plan sel).Slot c)
    (k : PageAt T (par.ticket slot))
    (origin : Bank→Prop) (B : Bank) (running : opened (borns M) origin (.step par slot) B)
    (rootPrecision : r.prec≤161*C*s^2) (e p edges : ℕ) :
    let Y := sourceState M par slot
    let record := Y.birth.job.immutable.payload
    let wires : List WireRead := (freshList Y k).map (fun h=>⟨freshBody h,List.replicate (freshOrdinal Y k h).val true⟩)
    ∃ F : pageFields record,
      (locate (occurrencePageWord Y.input k) record.payload.pages).result=some F ∧
      readCmdFee B e p edges (freshWord Y k)≤2^(6*H)*actualPacketPrefactor B record F p 0 wires := by
  let Y := sourceState M par slot
  let I := Y.input
  let wires : List WireRead := (freshList Y k).map (fun h=>⟨freshBody h,List.replicate (freshOrdinal Y k h).val true⟩)
  have used : OnPath (borns M) (compileOccurrence I).job (.step par slot) := .youngest par slot rfl
  exact actual_reached_ancestor_reader_geometric par slot I k (.step par slot) (borns M)
    used origin B running rootPrecision (e:=e) (p:=p) (edges:=edges) 0 wires

theorem real_ancestor_command_has_printed_reader_rate
    (M : OnlineMachine T key prec tw bw page rate)
    (par : Path sel r c) (slot : (Plan sel).Slot c) (owner : c.host.Row⊕c.host.Col)
    (arc : AncestorOrigin M par slot owner)
    (origin : Bank→Prop) (B : Bank) (running : opened (borns M) origin (.step par slot) B)
    (rootPrecision : r.prec≤161*C*s^2) (e p edges depth : ℕ) (wires : List WireRead) :
    let Y := sourceState M arc.atHome arc.slot
    let record := Y.birth.job.immutable.payload
    ∃ F : pageFields record,
      (locate (occurrencePageWord Y.input arc.pageId) record.payload.pages).result=some F ∧
      readCmdFee B e p edges (.packet Y.birth.job.identifier (occurrencePageWord Y.input arc.pageId) depth wires)≤
        2^(6*H)*actualPacketPrefactor B record F p depth wires := by
  let Y := sourceState M arc.atHome arc.slot
  let I := Y.input
  have used : OnPath (borns M) (compileOccurrence I).job (.step par slot) := .inherited par slot arc.own
  exact actual_reached_ancestor_reader_geometric arc.atHome arc.slot I arc.pageId (.step par slot) (borns M)
    used origin B running rootPrecision (e:=e) (p:=p) (edges:=edges) depth wires

variable {V : Type} [Fintype V]
variable {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {q ro co de edgew tc tj : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)

theorem actual_exterior_run_reader_has_printed_rate
    (hn : native≤m) {C : ℕ}
    (Cpos : 0<C) (Csmall : C≤physicalSize m native) (baseFit : base≤C*physicalSize m native)
    (pad : ℕ) (k : CanonicalPage m)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (alive : IsLive (X.seed pad) B)
    {p N : ℕ} (F : Frame f p) (dep : ℕ) (wires : List WireRead)
    (bits : List Bool) (size : bits.length=N) :
    let code : PageReadCode N key (pageKeyWidth m+pad) :=
      .generated (X.seed pad).identifier (widened pad (residentPageKey m k)).result dep wires
    let record := (X.seed pad).immutable.payload
    let field : pageFields record := X.chosenFields k
    let s := physicalSize m native
    (code.run X.hf F X.positive B bits).steps≤
      2^(6*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))*actualPacketPrefactor B record field p dep wires := by
  let code : PageReadCode N key (pageKeyWidth m+pad) :=
    .generated (X.seed pad).identifier (widened pad (residentPageKey m k)).result dep wires
  have h := raw_paged_read_bound X.hf F X.positive B code
    (J6R49Leaf.exterior_actual_page_format X pad k B alive dep wires) bits size
  exact h.trans (actual_exterior_reader_geometric X hn Cpos Csmall baseFit
    (physical_exterior_source_lambda_large m native hn) pad k B alive dep wires)

#print axioms actual_fresh_command_has_printed_reader_rate
#print axioms real_ancestor_command_has_printed_reader_rate
#print axioms actual_exterior_run_reader_has_printed_rate
end
end J6R66LeafTariff
