import J6R52TerminalAncestorDepth
import J6R36ChildFramedRouteWires

/-! Inherited Page route rows from the already-paid left side of the
same actual frame cache. The stored Page key/creator are read from
the mounted old origin word; its depth is extracted from the true
body, not supplied as a separate command or callback. -/
namespace J6R52Terminal
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths J6R51ParentFrames
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun J6R49SourceLayout J6R50SourceProducer J6R51Leaf J6R50Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 21000000
set_option maxRecDepth 3700
set_option Elab.async false

def compileKeptPage {w own key prec page : ℕ}
    (old : Word own) (tag : Origin key prec page)
    (book : List (Word w)) (frames : List (FramedEdge w own key prec page)) :
    Meter (Option (ReadCmd key page)) :=
  let origin := copyOrigin tag
  match origin.result.pageKey with
  | none => ⟨none,origin.steps+4⟩
  | some pg =>
    let requests := collectRetained old frames
    let hop := requestDepth requests.result
    match hop.result with
    | none => ⟨none,origin.steps+requests.steps+hop.steps+6⟩
    | some d =>
      let wires := emitWires book requests.result
      ⟨wires.result.map (.packet origin.result.stamp.creator pg d),
        origin.steps+requests.steps+hop.steps+wires.steps+8⟩

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (site : StoredSite T v key prec tw bw page)
variable (saved : CachedParentFrames site.site)
variable (inj : Function.Injective site.site.oldKey)

include inj in
theorem cached_retained_requests_same_actual_ports
    (u : OldAt T v) {root : Point f ell}
    (tr : Trace root (point v.parent.host u.val))
    (seed : PortAt root→List Bool)
    (body : ∀ p : PortAt (point v.parent.host u.val),
      (site.birth.native.physical.record p.val).body=tr.literal seed p) :
    let h := keptPorts T v site.birth.native.physical u
    let ext := tr.keep (retainedMove T v u)
    (collectRetained (site.site.oldKey u.val) saved.rows).result=
      h.map (fun p=>⟨(site.birth.native.physical.record (edge p.val).val).address,
        ext.literal seed p⟩) := by
  let J := site.birth.native
  let Q := site.site
  have eq := (actual_retained_request_file T v J site.birth.issuance Q.oldKey inj
    site.origins Q.pageKey Q.bank Q.bank_exact u tr seed body).1
  have pref := (native_frames_from_actual_selection T v J site.birth.issuance Q.aux Q.bank Q.bank_exact).1
  dsimp only at eq pref ⊢
  unfold retainedInput at eq
  dsimp only at eq
  rw [pref] at eq
  dsimp only at eq
  rw [exact_cached_frames site saved]
  exact Option.some.inj eq

def retainedSourceDepth {root : Point f ell} (u : OldAt T v)
    (tr : Trace root (point v.parent.host u.val)) : ℕ :=
  if (keptPorts T v site.birth.native.physical u).isEmpty then 0 else (tr.keep (retainedMove T v u)).depth

include inj in
theorem compiled_retained_page_from_actual_fields
    (u : OldAt T v) {root : Point f ell}
    (tr : Trace root (point v.parent.host u.val))
    (seed : PortAt root→List Bool)
    (seedTrue : ∀ p,∃ tail,seed p=true::tail)
    (body : ∀ p : PortAt (point v.parent.host u.val),
      (site.birth.native.physical.record p.val).body=tr.literal seed p)
    (pg : Word page) (hasPage : (site.origins u.val).pageKey=some pg) :
    let ports := keptPorts T v site.birth.native.physical u
    let ord := retainedEdgeOrder T v site.birth.native.physical u
    let t := tr.keep (retainedMove T v u)
    let op := compileKeptPage (site.site.oldKey u.val) (site.origins u.val)
      (cachedBook site saved).result saved.rows
    op.result=some (.packet (site.origins u.val).stamp.creator pg (retainedSourceDepth site u tr)
      (ports.map (fun p=>⟨t.literal seed p,List.replicate (ord.symm (edge p.val)).val true⟩))) ∧
      op.steps=originFee key prec page true+
        (3+(saved.rows.map (retainVisitFee (site.site.oldKey u.val))).sum)+
        (if ports.isEmpty then 3 else 4*t.depth+6)+
        (4+(ports.map (fun p=>sourceWireFee site.birth.port
          (ord.symm (edge p.val)).val (t.literal seed p).length)).sum)+8 := by
  let J := site.birth.native
  let Q := site.site
  let ports := keptPorts T v J.physical u
  let ext := tr.keep (retainedMove T v u)
  let ord := retainedEdgeOrder T v J.physical u
  let idx := fun (p : PortAt (retainedMove T v u).next)=>ord.symm (edge p.val)
  let names (j : Fin v.child.edges) := (J.physical.record (ord j).val).address
  let req := collectRetained (Q.oldKey u.val) saved.rows
  let book := cachedBook site saved
  have H := cached_retained_requests_same_actual_ports site saved inj u tr seed body
  have E : req.result=ports.map (fun p=>⟨names (idx p),ext.literal seed p⟩) := by
    refine H.trans ?_
    apply List.map_congr_left
    intro p _
    change WireRequest.mk (J.physical.record (edge p.val).val).address (ext.literal seed p) =
      WireRequest.mk (J.physical.record (ord (idx p)).val).address (ext.literal seed p)
    rw [show ord (idx p)=edge p.val from ord.apply_symm_apply _]
  have distinct : Function.Injective names :=
    J.physical.distinct.comp (Subtype.val_injective.comp ord.injective)
  have keys : book.result=List.ofFn names :=
    (cached_book_exact site saved).1.trans (exact_child_edge_book T v J).1
  obtain ⟨kept,fee⟩ := source_wire_tape book.result names distinct keys ports (ext.literal seed) idx
    req.result E
  have depF : requestDepth req.result=
      ⟨some (retainedSourceDepth site u tr),if ports.isEmpty then 3 else 4*ext.depth+6⟩ := by
    unfold retainedSourceDepth
    rw [E,show keptPorts T v site.birth.native.physical u=ports from rfl]
    cases same : ports with
    | nil => rfl
    | cons p rest =>
      exact request_depth_from_true_trace ext seed seedTrue p (names (idx p)) _
  have total : req.steps=3+(saved.rows.map (retainVisitFee (Q.oldKey u.val))).sum :=
    (collect_retained_exact (Q.oldKey u.val) saved.rows).2
  dsimp only [compileKeptPage] at kept fee ⊢
  rw [copy_origin_exact,hasPage]
  dsimp only
  rw [show requestDepth (collectRetained (Q.oldKey u.val) saved.rows).result=_ from depF]
  dsimp only
  rw [show (emitWires book.result req.result).result=_ from kept,
    show (emitWires book.result req.result).steps=_ from fee,show req.steps=_ from total]
  exact ⟨rfl,rfl⟩

end
#print axioms cached_retained_requests_same_actual_ports
#print axioms compiled_retained_page_from_actual_fields
end J6R52Terminal
