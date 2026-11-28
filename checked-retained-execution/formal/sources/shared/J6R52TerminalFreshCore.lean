import J6R51ParentFramesCache
import J6R51LeafFreshRead
import J6R50LeafRead

/-! Read the true edge key book from the *same* previously paid frame
cache. Compile a literal newly born Page's wire command from these
right-hand fields, billing every true key seek and copy but not
buying the already-installed sidecar or descriptor header again. -/
namespace J6R52Terminal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths J6R51ParentFrames
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun J6R49SourceLayout J6R50SourceProducer J6R51Leaf J6R50Leaf J6R48RawRoute
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 3700
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (site : StoredSite T v key prec tw bw page)
variable (saved : CachedParentFrames site.site)

theorem exact_cached_frames :
    saved.rows=(halfOrder T v site.birth.native.physical).map site.site.frame :=
  Option.some.inj (saved.exactRows.symm.trans (true_site_issuance site.site).2.2.2)

def cachedBook : Meter (List (Word site.birth.port)) :=
  frameKeys saved.rows

theorem cached_book_exact :
    let book := cachedBook site saved
    book.result=(storedBook site).result ∧ book.steps=
       3+(saved.rows.map (fun x=>3*site.birth.port+5+framedIncidenceFee x)).sum := by
  dsimp only [cachedBook]
  rw [frame_keys_exact]
  constructor
  · dsimp only
    rw [exact_cached_frames site saved,List.map_map,(stored_book_actual site).1,
      ← get_half_by_actual_order T v site.birth.native.physical,List.map_ofFn]
    rfl
  · rfl

theorem cached_fresh_requests (k : PageAt T v) :
    let req := scanFresh (occurrencePageWord site.input k) saved.rows
    req.result=(freshList site k).map (fun h=>⟨
      childKey T v site.birth.native.physical
        (actualEdgeOrder T v site.birth.native.physical (freshOrdinal site k h)),
      freshBody h⟩) := by
  dsimp only
  rw [scan_fresh_exact,exact_cached_frames site saved,fresh_requests_use_physical_page]
  dsimp only
  apply List.map_congr_left
  intro h _
  let ord := actualEdgeOrder T v site.birth.native.physical
  have idx : ord (freshOrdinal site k h)=(childHalves T v).symm h.val :=
    ord.apply_symm_apply _
  have keyEq : childKey T v site.birth.native.physical (ord (freshOrdinal site k h))=
      (site.birth.native.physical.record h.val.val).address := by
    unfold childKey
    rw [idx,Equiv.apply_symm_apply]
  change WireRequest.mk (site.site.frame h.val).right.id.edge (site.site.frame h.val).right.body = _
  rw [frame_exact_selected_address site h.val,frame_has_source_body site h,keyEq]

end

def compileFreshOne {w own key prec page : ℕ}
    (creator : Word key) (book : List (Word w))
    (frame : List (FramedEdge w own key prec page)) (pg : Word page) :
    Meter (Option (ReadCmd key page)) :=
  let requests := scanFresh pg frame
  let wires := emitWires book requests.result
  let a := copyFixed creator
  let p := copyFixed pg
  ⟨wires.result.map (.packet a.result p.result 0),
    requests.steps+wires.steps+a.steps+p.steps+7⟩

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (site : StoredSite T v key prec tw bw page)
variable (saved : CachedParentFrames site.site)

def freshWord (k : PageAt T v) : ReadCmd key page :=
  .packet site.birth.job.identifier (occurrencePageWord site.input k) 0
    ((freshList site k).map (fun h=>⟨freshBody h,List.replicate (freshOrdinal site k h).val true⟩))

theorem compile_cached_fresh_one (k : PageAt T v) :
    let pg := occurrencePageWord site.input k
    let books := cachedBook site saved
    let op := compileFreshOne site.birth.job.identifier books.result saved.rows pg
    op.result=some (freshWord site k) ∧
      op.steps=3+(saved.rows.map (freshVisitFee pg)).sum+
        (4+((freshList site k).map
          (fun h=>sourceWireFee site.birth.port (freshOrdinal site k h).val (freshBody h).length)).sum)+
        (3*key+1)+(3*page+1)+7 := by
  let pg := occurrencePageWord site.input k
  let books := cachedBook site saved
  let ord := actualEdgeOrder T v site.birth.native.physical
  let keyAt (j : Fin v.child.edges) := childKey T v site.birth.native.physical (ord j)
  have keys : books.result=List.ofFn keyAt :=
    (cached_book_exact site saved).1.trans (stored_book_actual site).1
  have unique : Function.Injective keyAt :=
    (child_key_injective T v site.birth.native.physical).comp ord.injective
  obtain ⟨wires,fee⟩ := source_wire_tape books.result keyAt unique keys (freshList site k)
    freshBody (freshOrdinal site k) (scanFresh pg saved.rows).result (cached_fresh_requests site saved k)
  have price := congrArg Meter.steps (scan_fresh_exact pg saved.rows)
  dsimp only [compileFreshOne] at wires fee price ⊢
  rw [show (emitWires books.result (scanFresh pg saved.rows).result).result=_ from wires,
    show (emitWires books.result (scanFresh pg saved.rows).result).steps=_ from fee,
    copy_fixed_exact,copy_fixed_exact,show (scanFresh pg saved.rows).steps=
      3+(saved.rows.map (freshVisitFee pg)).sum from price]
  exact ⟨rfl,rfl⟩

end
#print axioms exact_cached_frames
#print axioms cached_book_exact
#print axioms cached_fresh_requests
#print axioms compile_cached_fresh_one
end J6R52Terminal
