import J6R62LeafFreshFormat
import J6R15PlantedIdentityMesh

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 42000000
set_option maxRecDepth 5500

/-! Proof-side syntax certification of the existing retained compiler.
Keep the ancestor's actual creator and immutable packing; no fresh
atlas size or packet format is imposed on a retained packet. -/
namespace J6R62Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
open J6R48Leaf J6R57Public J6R48RawRoute

theorem saved_gate_compile_format {f : ℤ[X]} {ell key prec tw bw pg w W own : ℕ}
    (B : PageBank f ell key prec tw bw pg) (edges b : ℕ)
    (book : List (Word W)) (fs : List (FramedEdge W own key prec pg))
    (id : Word own) (gate : CodeGate (Word w)) (cmd : ReadCmd key pg)
    (hit : (compileSavedGate b book fs id gate).result=some cmd) :
    ReadFormat B edges cmd := by
  dsimp only [compileSavedGate] at hit
  split at hit
  · dsimp only at hit
    contradiction
  · rename_i g eq
    dsimp only at hit
    cases ready : (compileCurrentGate b book g).result with
    | none => simp [ready] at hit
    | some body =>
      have eq : ReadCmd.gate b body=cmd := by simpa only [ready,Option.map_some,Option.some.injEq] using hit
      subst cmd
      trivial

theorem retained_page_compile_address {key prec pg W own : ℕ}
    (book : List (Word W)) (fs : List (FramedEdge W own key prec pg))
    (id : Word own) (tag : Origin key prec pg) (cmd : ReadCmd key pg)
    (hit : (compileKeptPage id tag book fs).result=some cmd) :
    ∃ kp depth wires,tag.pageKey=some kp ∧ cmd=ReadCmd.packet tag.stamp.creator kp depth wires := by
  let rs := (collectRetained id fs).result
  dsimp only [compileKeptPage] at hit
  rw [copy_origin_exact] at hit
  dsimp only at hit
  cases h : tag.pageKey with
  | none =>
    rw [h] at hit
    contradiction
  | some kp =>
    rw [h] at hit
    dsimp only at hit
    change (match (requestDepth rs).result with
      | none => (⟨none,originFee key prec pg true+(collectRetained id fs).steps+
          (requestDepth rs).steps+6⟩ : Meter (Option (ReadCmd key pg)))
      | some d => ⟨(emitWires book rs).result.map (.packet tag.stamp.creator kp d),
          originFee key prec pg true+(collectRetained id fs).steps+
          (requestDepth rs).steps+(emitWires book rs).steps+8⟩).result=some cmd at hit
    cases hdep : (requestDepth rs).result with
    | none =>
      rw [hdep] at hit
      contradiction
    | some depth =>
      rw [hdep] at hit
      dsimp only at hit
      cases hw : (emitWires book rs).result with
      | none => simp [hw] at hit
      | some wires =>
        have actual : ReadCmd.packet tag.stamp.creator kp depth wires=cmd := by
          simpa only [hw,Option.map_some,Option.some.injEq] using hit
        exact ⟨kp,depth,wires,rfl,actual.symm⟩

theorem gathered_item_was_actually_acquired {A D : Type*} (stride : ℕ) (one : A→Meter (Option D))
    (xs : List A) :
    ∀ out, (gatherOptions stride one xs).result=some out →
      ∀ d∈out,∃ a∈xs,(one a).result=some d := by
  induction xs with
  | nil =>
    intro out eq d used
    obtain rfl := Option.some.inj eq
    simp at used
  | cons x xs ih =>
    intro out eq d used
    dsimp only [gatherOptions] at eq
    cases hx : (one x).result with
    | none => rw [hx] at eq; contradiction
    | some k =>
      rw [hx] at eq
      dsimp only [Option.bind] at eq
      cases ht : (gatherOptions stride one xs).result with
      | none => rw [ht] at eq; contradiction
      | some tail =>
        rw [ht] at eq
        have eq' : k::tail=out := Option.some.inj eq
        subst out
        rcases List.mem_cons.mp used with here|there
        · exact ⟨x,List.mem_cons_self,here ▸ hx⟩
        · obtain ⟨a,ha,got⟩ := ih tail ht d there
          exact ⟨a,List.mem_cons_of_mem _ ha,got⟩

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
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

theorem true_exterior_seed_packet_format
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (live : IsLive (X.seed pad) B)
    (k : CanonicalPage m) (edges depth : ℕ) (wires : List WireRead) :
    ReadFormat B edges (.packet (X.seed pad).identifier
      (J6R34RootAtlas.widened pad (residentPageKey m k)).result depth wires) := by
  let R := (X.seed pad).immutable.payload
  let D := X.chosenFields k
  refine ⟨R,live.2,rfl,rfl,D,true_seed_payload_page X pad k,?_⟩
  obtain ⟨rows,_,_,_,_,_,_,modes,hm,_,codes⟩ := stable_seed_true_page_law X k
  constructor
  · change X.context.center∈P1DyadicGrid.grid (a m)
    rw [X.signedCentre]
    exact J6R15PlantedIdentity.centre_in_grid m X.centre
  · exact X.hq
  · change D.modes.length+1≤2^X.context.codeWidth.val
    change D.modes=List.ofFn modes at hm
    rw [X.codeTruth,hm,List.length_ofFn,Nat.add_comm]
    exact Nat.le_of_lt X.codeValid
  · change D.rows.length<2^q
    change D.rows=_ at rows
    rw [rows,List.length_map]
    exact actual_root_row_count_fits X k
  · change ∀ j : Fin D.modes.length,(D.modes.get j).code=encodeBits X.context.codeWidth.val j.succ.val
    rw [X.codeTruth]
    exact list_modes_have_source_codes modes X.code codes D.modes hm

theorem actual_ancestor_packet_format
    (u : c.host.Row⊕c.host.Col) (anc : AncestorOrigin M p w u)
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (live : opened (borns M) rootLive (Path.step p w) B) (edges depth : ℕ) (wires : List WireRead) :
    let Y := sourceState M anc.atHome anc.slot
    ReadFormat B edges (.packet Y.birth.job.identifier (occurrencePageWord Y.input anc.pageId) depth wires) := by
  let Y := sourceState M anc.atHome anc.slot
  let I := Y.input
  have ancLive : OnPath (borns M) Y.birth.job (Path.step p w) := .inherited p w anc.own
  exact actual_format_in_native_or_printed_width I.native.result
    (A1R12.padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)) I.hOld
    (Classical.choice (occurrence_real_receipt I)) anc.pageId I.centre I.codeExact
    (by simpa only [Nat.add_comm] using Nat.le_of_lt I.codeFit)
    I.width (Path.step p w) (borns M) ancLive rootLive B live edges depth wires

theorem old_command_from_true_provenance_has_format
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate) (gateWidth : gate.created.val=base)
    (A : OwnerTerminalInput X p w (sourceState M p w)) (u : OldAt T (p.ticket w))
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B) (live : opened (borns M) rootLive (Path.step p w) B)
    (cmd : ReadCmd key (pageKeyWidth m+pad))
    (hit : (compileByOwnerData (p.ticket w).child.edges (cachedBook (sourceState M p w) A.saved).result
      A.saved.rows ((sourceState M p w).site.oldKey u.val)
      (parentData (sourceState M p w) (gateHistory T (bootGates X) p) u.val)).result=some cmd) :
    ReadFormat B (p.ticket w).child.edges cmd := by
  let Y := sourceState M p w
  let book := (cachedBook Y A.saved).result
  let who := Y.site.oldKey u.val
  let origin := Y.origins u.val
  have k := actual_old_sources_from_one_printed_boot X M gate boot p w gateWidth u
  dsimp only [compileByOwnerData,parentData] at hit
  cases k with
  | original x tr body code =>
    rw [code] at hit
    exact saved_gate_compile_format B (p.ticket w).child.edges (p.ticket w).child.edges
      book A.saved.rows who _ cmd hit
  | exterior k tr tag body noGate =>
    rw [noGate] at hit
    obtain ⟨pg,dep,wires,h,rfl⟩ := retained_page_compile_address book A.saved.rows who origin cmd hit
    change origin=_ at tag
    rw [tag] at h ⊢
    have pgEq := Option.some.inj h
    rw [←pgEq]
    exact true_exterior_seed_packet_format X B openRoot k _ _ _
  | native anc noGate =>
    rw [noGate] at hit
    obtain ⟨pg,dep,wires,h,rfl⟩ := retained_page_compile_address book A.saved.rows who origin cmd hit
    have tag := anc.tag
    change origin=_ at tag
    rw [tag] at h ⊢
    have pgEq := Option.some.inj h
    rw [←pgEq]
    exact actual_ancestor_packet_format X M p w u.val anc rootLive B live _ _ _

theorem every_actual_retained_owner_command_is_formatted
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate) (gateWidth : gate.created.val=base)
    (A : OwnerTerminalInput X p w (sourceState M p w))
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B) (live : opened (borns M) rootLive (Path.step p w) B)
    (older : List (ReadCmd key (pageKeyWidth m+pad)))
    (compiled : (oldCompiler X p w (sourceState M p w) A).result=some older)
    (cmd : ReadCmd key (pageKeyWidth m+pad)) (atOld : cmd∈older) :
    ReadFormat B (p.ticket w).child.edges cmd := by
  let Y := sourceState M p w
  let book := (cachedBook Y A.saved).result
  let keys := (selectOwnerKeys (word (p.ticket w).groupAt.val) A.headers.raw).result
  let one := compileByRoster (p.ticket w).child.edges book A.saved.rows A.roster.raw
  let O := (readOldVertices Y.site A.headers).result
  change (gatherOptions 1 one keys).result=some older at compiled
  obtain ⟨id,used,hit⟩ := gathered_item_was_actually_acquired 1 one keys older compiled cmd atOld
  have ord : keys=O.rows.map (nativeRowKey Y.site) :=
    (exact_old_vertices_from_grouped_headers Y.site A.headers).1.symm.trans O.exact
  rw [ord] at used
  obtain ⟨owner,_,rfl⟩ := List.mem_map.mp used
  let u := physicalChildRows (T:=T) (v:=p.ticket w) owner
  have eq := compile_by_same_owner_roster A.roster A.inj u.val book A.saved.rows (p.ticket w).child.edges
  change (compileByRoster (p.ticket w).child.edges book A.saved.rows A.roster.raw
    (Y.site.oldKey u.val)).result=some cmd at hit
  rw [eq] at hit
  exact old_command_from_true_provenance_has_format X M p w gate boot gateWidth A u rootLive B openRoot live cmd hit

#print axioms saved_gate_compile_format
#print axioms retained_page_compile_address
#print axioms gathered_item_was_actually_acquired
#print axioms true_exterior_seed_packet_format
#print axioms actual_ancestor_packet_format
#print axioms old_command_from_true_provenance_has_format
#print axioms every_actual_retained_owner_command_is_formatted
end
end J6R62Leaf
