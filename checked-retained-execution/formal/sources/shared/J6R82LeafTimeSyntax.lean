import J6R66LeafTariffWires
import J6R62LeafOldFormat
import J6R62LeafCensus
import J6R62LeafSized

/-! Obtain command sizes from the actual ordered emitter, not from
correctness/format of an unspecified reader. -/
namespace J6R82LeafTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R12
open J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R36ChildFramedRoute J6R51ParentFrames J6R53TerminalGate J6R53OldOwner J6R49SourceLayout
open J6R66LeafTariff
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxHeartbeats 35000000
set_option maxRecDepth 5000

private theorem mapped_gates_have_actual_port_count {D A B : Type}
    (b : ℕ) (ports : List D) (read : D→Meter (Option A))
    (make : List A→CodeGate B) (arity : ∀ xs,gatePorts (make xs)=xs.length)
    {code : CodeGate B} (ok : (gatherOptions b read ports).result.map make=some code) :
    gatePorts code=ports.length := by
  cases h : (gatherOptions b read ports).result with
  | none => simp [h] at ok
  | some ds =>
    have out : make ds=code := Option.some.inj (by simpa only [h,Option.map_some] using ok)
    rw [←out,arity]
    exact accepted_gather_census b read ports ds h

theorem paid_reroute_keeps_arity {w W : ℕ} (bank : List (RefRow w (Word W)))
    (g : CodeGate (Word w)) (new : CodeGate (Word W))
    (hit : (rerouteGate bank g).result=some new) :
    gatePorts new=gatePorts g := by
  cases g with
  | free =>
    have e : CodeGate.free=new := Option.some.inj hit
    subst new
    rfl
  | equal ports =>
    exact mapped_gates_have_actual_port_count W ports (fun a=>locate a bank) CodeGate.equal (fun _=>rfl) hit
  | clause ports signs =>
    exact mapped_gates_have_actual_port_count W ports (fun a=>locate a bank)
      (fun ds=>CodeGate.clause ds (copyBytes signs).result) (fun _=>rfl) hit

theorem paid_ordinals_keep_gate_arity {W b : ℕ} (book : List (Word W))
    (g : CodeGate (Word W)) (new : CodeGate (Word b))
    (hit : (compileCurrentGate b book g).result=some new) :
    gatePorts new=gatePorts g := by
  cases g with
  | free =>
    have e : CodeGate.free=new := Option.some.inj hit
    subst new
    rfl
  | equal ports =>
    exact mapped_gates_have_actual_port_count b ports (fun a=>findOrdinal b a book) CodeGate.equal (fun _=>rfl) hit
  | clause ports signs =>
    exact mapped_gates_have_actual_port_count b ports (fun a=>findOrdinal b a book)
      (fun ds=>CodeGate.clause ds (copyBytes signs).result) (fun _=>rfl) hit

theorem compiled_old_gate_has_its_actual_width_and_arity {w W own key prec page : ℕ}
    (b : ℕ) (book : List (Word W)) (rows : List (FramedEdge W own key prec page))
    (old : Word own) (g : CodeGate (Word w)) (cmd : ReadCmd key page)
    (hit : (compileSavedGate b book rows old g).result=some cmd) :
    ∃ new : CodeGate (Word b),cmd=.gate b new ∧ gatePorts new=gatePorts g := by
  let bank := (suffixTable w (collectRetained old rows).result).result
  cases h : (rerouteGate bank g).result with
  | none => simp [compileSavedGate,bank,h] at hit
  | some renamed =>
    cases e : (compileCurrentGate b book renamed).result with
    | none => simp [compileSavedGate,bank,h,e] at hit
    | some new =>
      have result : ReadCmd.gate b new=cmd := by
        simpa only [compileSavedGate,show (rerouteGate (suffixTable w (collectRetained old rows).result).result g).result
          =some renamed from h,e,Option.map_some,Option.some.injEq] using hit
      exact ⟨new,result.symm,(paid_ordinals_keep_gate_arity book renamed new e).trans
        (paid_reroute_keeps_arity bank g renamed h)⟩

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
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
variable (A : OwnerTerminalInput X p w (sourceState M p w))

theorem actual_book_and_frames_are_child_size :
    (cachedBook (sourceState M p w) A.saved).result.length=((p.ticket w).child.edges) ∧ A.saved.rows.length=((p.ticket w).child.edges) := by
  have size := (canonical_terminal_table_censuses X p w (sourceState M p w) A).1
  have keys := (cached_book_exact (sourceState M p w) A.saved).1.trans (stored_book_actual (sourceState M p w)).1
  exact ⟨(congrArg List.length keys).trans List.length_ofFn,size⟩

theorem actual_ordered_old_command_has_owner_producer
    (older : List Cmd) (compiled : (oldCompiler X p w (sourceState M p w) A).result=some older)
    (cmd : Cmd) (inside : cmd∈older) :
    ∃ u : OldAt T (p.ticket w),
      (compileByOwnerData ((p.ticket w).child.edges) (cachedBook (sourceState M p w) A.saved).result A.saved.rows ((sourceState M p w).site.oldKey u.val)
        (parentData (sourceState M p w) (gateHistory T (bootGates X) p) u.val)).result=some cmd := by
  let book := (cachedBook (sourceState M p w) A.saved).result
  let keys := (selectOwnerKeys (word (p.ticket w).groupAt.val) A.headers.raw).result
  let one := compileByRoster ((p.ticket w).child.edges) book A.saved.rows A.roster.raw
  let O := (readOldVertices (sourceState M p w).site A.headers).result
  change (gatherOptions 1 one keys).result=some older at compiled
  obtain ⟨id,used,hit⟩ := gathered_item_was_actually_acquired 1 one keys older compiled cmd inside
  have ord : keys=O.rows.map (nativeRowKey (sourceState M p w).site) :=
    (exact_old_vertices_from_grouped_headers (sourceState M p w).site A.headers).1.symm.trans O.exact
  rw [ord] at used
  obtain ⟨owner,_,rfl⟩ := List.mem_map.mp used
  let u := physicalChildRows (T:=T) (v:=p.ticket w) owner
  have eq := compile_by_same_owner_roster A.roster A.inj u.val book A.saved.rows ((p.ticket w).child.edges)
  change (compileByRoster ((p.ticket w).child.edges) book A.saved.rows A.roster.raw
    ((sourceState M p w).site.oldKey u.val)).result=some cmd at hit
  rw [eq] at hit
  exact ⟨u,hit⟩

theorem actual_input_gate_has_observed_arity (u : OldAt T (p.ticket w))
    (g : CodeGate (Word (pageKeyWidth m+J6Mesh.a m)))
    (yes : (parentData (sourceState M p w) (gateHistory T (bootGates X) p) u.val).gateCode=some g) :
    gatePorts g≤observedGateWidth A.roster.raw := by
  have member : (⟨(sourceState M p w).site.oldKey u.val,parentData (sourceState M p w) (gateHistory T (bootGates X) p) u.val⟩ :
      RefRow (sourceState M p w).site.ownerWidth (OwnerData (pageKeyWidth m+J6Mesh.a m) key prec (pageKeyWidth m+pad)))∈
      A.roster.raw := by
    rw [A.roster.exactRows]
    exact List.mem_map.mpr ⟨u.val,A.roster.complete _,rfl⟩
  exact (gate_width_is_observed A.roster.raw _ member g yes).1

theorem actual_kept_page_limited_by_its_paid_book
    (u : OldAt T (p.ticket w)) (addr : Word key) (pageID : Word (pageKeyWidth m+pad))
    (depth : ℕ) (wires : List WireRead)
    (hit : (compileKeptPage ((sourceState M p w).site.oldKey u.val) ((sourceState M p w).origins u.val) (cachedBook (sourceState M p w) A.saved).result A.saved.rows).result=
      some (.packet addr pageID depth wires)) :
    let U := observedFrameWidth A.saved.rows
    depth≤U ∧ wires.length≤((p.ticket w).child.edges) ∧ ∀ a,
      rawWireFee (depth+a+2) wires≤((p.ticket w).child.edges)*(3*U+4*((p.ticket w).child.edges)+(U+a+2)+12) := by
  let U := observedFrameWidth A.saved.rows
  let fs := A.saved.rows
  let book := (cachedBook (sourceState M p w) A.saved).result
  have geom := actual_book_and_frames_are_child_size X M p w A
  have cb := actual_kept_packet_wire_tariff ((sourceState M p w).site.oldKey u.val) ((sourceState M p w).origins u.val) book fs
    (frame_width_is_observed fs) addr pageID depth wires hit
  refine ⟨(cb 0).1,(cb 0).2.1.trans_eq geom.2,?_⟩
  intro a
  have cost := (cb a).2.2
  change _≤fs.length*(3*U+4*book.length+(U+a+2)+12) at cost
  rw [show fs.length=((p.ticket w).child.edges) from geom.2,show book.length=((p.ticket w).child.edges) from geom.1] at cost
  exact cost

theorem actual_fresh_page_limited_by_its_paid_book (k : PageAt T (p.ticket w)) :
    let U := observedFrameWidth A.saved.rows
    let wires : List WireRead := (freshList (sourceState M p w) k).map
      (fun h=>⟨freshBody h,List.replicate (freshOrdinal (sourceState M p w) k h).val true⟩)
    wires.length≤((p.ticket w).child.edges) ∧ ∀ a, rawWireFee (0+a+2) wires≤((p.ticket w).child.edges)*(3*U+4*((p.ticket w).child.edges)+(U+a+2)+12) := by
  let U := observedFrameWidth A.saved.rows
  let fs := A.saved.rows
  let book := (cachedBook (sourceState M p w) A.saved).result
  let wires : List WireRead := (freshList (sourceState M p w) k).map
    (fun h=>⟨freshBody h,List.replicate (freshOrdinal (sourceState M p w) k h).val true⟩)
  have geom := actual_book_and_frames_are_child_size X M p w A
  have cb := actual_fresh_packet_wire_tariff (sourceState M p w).birth.job.identifier book fs
    (frame_width_is_observed fs) (occurrencePageWord (sourceState M p w).input k) 0 wires
    (compile_cached_fresh_one (sourceState M p w) A.saved k).1
  refine ⟨(cb 0).2.1.trans_eq geom.2,?_⟩
  intro a
  have cost := (cb a).2.2
  change _≤fs.length*(3*U+4*book.length+(a+2)+12) at cost
  rw [show fs.length=((p.ticket w).child.edges) from geom.2,show book.length=((p.ticket w).child.edges) from geom.1] at cost
  exact cost.trans (Nat.mul_le_mul_left _ (by omega))

#print axioms paid_reroute_keeps_arity
#print axioms paid_ordinals_keep_gate_arity
#print axioms compiled_old_gate_has_its_actual_width_and_arity
#print axioms actual_book_and_frames_are_child_size
#print axioms actual_ordered_old_command_has_owner_producer
#print axioms actual_input_gate_has_observed_arity
#print axioms actual_kept_page_limited_by_its_paid_book
#print axioms actual_fresh_page_limited_by_its_paid_book
end
end J6R82LeafTime
