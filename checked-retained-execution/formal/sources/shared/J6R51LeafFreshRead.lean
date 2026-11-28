import J6R51LeafFreshTape
import J6R49SourceLayoutPageKeys

/-! Connect the metered right-frame scan and ordinal encoder to
the physical Page of exactly the stored call. Empty pages use
their actual immutable roster keys and have an empty wire list. -/
namespace J6R51Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R21Ancestor J6R15ModeCost
open J6R41StructuredAllPaths J6R36ChildFramedRoute J6R34ChildPath J6R50Leaf
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R50SourceProducer J6R49SourceLayout
open J6R27OriginalGate J6R9PacketScopes P11FullPacking
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4200

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

def physicalPage (h : HalfAt T v) : PageAt T v :=
  atPacket (layout T v) (edge h.val)

abbrev FreshHalf (k : PageAt T v) := {h : HalfAt T v//physicalPage h=k}

def asFreshPort {k : PageAt T v} (h : FreshHalf k) : PortAt (bornPoint T v k) :=
  ⟨.inr h.val,congrArg Sum.inr h.property⟩

theorem fresh_port_edge {k : PageAt T v} (h : FreshHalf k) :
    edge (asFreshPort h).val=h.val := rfl

theorem fresh_port_surjective (k : PageAt T v) : Function.Surjective (asFreshPort (k:=k)) := by
  rintro ⟨p,h⟩
  cases p with
  | inl e => cases h
  | inr e => exact ⟨⟨e,Sum.inr.inj h⟩,rfl⟩

variable (site : StoredSite T v key prec tw bw page)

def freshList (k : PageAt T v) : List (FreshHalf k) :=
  scanSubtype (fun h : HalfAt T v=>physicalPage h=k)
    (halfOrder T v site.birth.native.physical)

theorem fresh_list_complete (k : PageAt T v) (p : PortAt (bornPoint T v k)) :
    p∈(freshList site k).map asFreshPort := by
  obtain ⟨h,rfl⟩ := fresh_port_surjective k p
  apply List.mem_map_of_mem
  exact (scan_subtype_mem _ _ h).mpr ((half_order_complete T v site.birth.native.physical).2 h.val)

theorem frame_fresh_key (h : HalfAt T v) :
    (site.site.frame h).right.origin.pageKey=some (occurrencePageWord site.input (physicalPage h)) := by
  change some (site.site.pageKey (physicalPage h))=_
  rw [site.canonical]

theorem frame_exact_selected_address (h : HalfAt T v) :
    (site.site.frame h).right.id.edge=(site.birth.native.physical.record h.val).address := rfl

theorem fresh_requests_use_physical_page (k : PageAt T v) :
    let frames := (halfOrder T v site.birth.native.physical).map site.site.frame
    frames.filterMap (chooseFresh (occurrencePageWord site.input k))=
      (freshList site k).map (fun h=>requestView (site.site.frame h.val).right) := by
  dsimp only [freshList,scanSubtype]
  rw [List.filterMap_map,List.map_filterMap]
  apply List.filterMap_congr
  intro h _
  have test : (cmpAddr (occurrencePageWord site.input k) (occurrencePageWord site.input (physicalPage h))).result=true ↔
      physicalPage h=k := by
    rw [(cmpAddr_exact _ _).1,(occurrence_page_word_injective site.input).eq_iff,eq_comm]
  by_cases eq : physicalPage h=k
  · simp only [Function.comp_apply,chooseFresh,frame_fresh_key site h,if_pos (test.mpr eq),dif_pos eq,
      Option.map_some]
  · simp only [Function.comp_apply,chooseFresh,frame_fresh_key site h,
      if_neg (fun x=>eq (test.mp x)),dif_neg eq,Option.map_none]

def freshOrdinal (k : PageAt T v) (h : FreshHalf k) : Fin v.child.edges :=
  (actualEdgeOrder T v site.birth.native.physical).symm ((childHalves T v).symm h.val)

def freshBody {k : PageAt T v} (h : FreshHalf k) : List Bool :=
  originSeed (layout T v) (axis T v) v.groupAt k (asFreshPort h)

theorem frame_has_source_body {k : PageAt T v} (h : FreshHalf k) :
    (site.site.frame h.val).right.body=freshBody h :=
  (native_page_body_at_issue site.site k (asFreshPort h) (word 0)).2.1

/-- Both the selected old table and the new Page's route are prepared
here, so neither is treated as a free operation when not already paid. -/
def paidFreshWires (id : Word page) : Meter (Option (List WireRead)) :=
  let req := paidFreshRequests site id
  let book := storedBook site
  match req.result with
  | none => ⟨none,req.steps+4⟩
  | some fields =>
    let out := emitWires book.result fields
    ⟨out.result,req.steps+book.steps+out.steps+5⟩

theorem same_fresh_leaf_wires_and_fee (k : PageAt T v) :
    let active := freshList site k
    let request := paidFreshRequests site (occurrencePageWord site.input k)
    let book := storedBook site
    let out := paidFreshWires site (occurrencePageWord site.input k)
    out.result=some (active.map (fun h=>⟨freshBody h,List.replicate (freshOrdinal site k h).val true⟩)) ∧
      out.steps=request.steps+book.steps+9+
        (active.map (fun h=>sourceWireFee site.birth.port (freshOrdinal site k h).val (freshBody h).length)).sum := by
  let act := freshList site k
  let req := paidFreshRequests site (occurrencePageWord site.input k)
  let book := storedBook site
  let ord := actualEdgeOrder T v site.birth.native.physical
  let keyAt := fun j=>childKey T v site.birth.native.physical (ord j)
  have inj : Function.Injective keyAt :=
    (child_key_injective T v site.birth.native.physical).comp ord.injective
  have request : req.result=some (act.map (fun h=>⟨keyAt (freshOrdinal site k h),freshBody h⟩)) := by
    change (paidFreshRequests site (occurrencePageWord site.input k)).result=_
    rw [fresh_requests_from_same_issued_frames,fresh_requests_use_physical_page]
    dsimp only
    apply congrArg some
    apply List.map_congr_left
    intro h _
    have key : keyAt (freshOrdinal site k h)=(site.birth.native.physical.record h.val.val).address := by
      have p : ord (freshOrdinal site k h)=(childHalves T v).symm h.val :=
        ord.apply_symm_apply _
      change (site.birth.native.physical.record
        ((childHalves T v) (ord (freshOrdinal site k h))).val).address=_
      rw [p,Equiv.apply_symm_apply]
    change WireRequest.mk (site.site.frame h.val).right.id.edge (site.site.frame h.val).right.body = _
    rw [frame_exact_selected_address site h.val,frame_has_source_body site h,key]
  have out := source_wire_tape book.result keyAt inj (stored_book_actual site).1
    act freshBody (freshOrdinal site k) (act.map (fun h=>⟨keyAt (freshOrdinal site k h),freshBody h⟩)) rfl
  obtain ⟨e,cost⟩ := out
  dsimp only at e cost ⊢
  unfold paidFreshWires
  dsimp only
  rw [show (paidFreshRequests site (occurrencePageWord site.input k)).result=_ from request]
  dsimp only
  rw [e,cost]
  constructor
  · rfl
  · dsimp only [act]
    omega

#print axioms fresh_list_complete
#print axioms fresh_requests_use_physical_page
#print axioms same_fresh_leaf_wires_and_fee
end
end J6R51Leaf
