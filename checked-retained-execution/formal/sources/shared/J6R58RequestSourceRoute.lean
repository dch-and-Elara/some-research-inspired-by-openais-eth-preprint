import J6R51ParentFramesCache
import J6R50SourceProducerOnline

/-! Decode a route by scanning the current live cached frame file.
The selected edge address and side choose its original left owner
word or its actual born Page word. The touched opaque lane fields
are traversed and charged, not guessed from a typed incidence map. -/
namespace J6R58RequestSource
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R50SourceProducer
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R51ParentFrames J6R49SourceLayout J6R48RawRoute J6ActiveRun
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15600000
set_option maxRecDepth 4100
set_option Elab.async false

abbrev Endpoint (own page : ℕ) := Word own ⊕ Word page

def copyEndpoint {w own key prec page : ℕ} (col : Bool) (x : FramedEdge w own key prec page) :
    Meter (Option (Endpoint own page)) :=
  if col then
    let C := copyOrigin x.right.origin
    ⟨C.result.pageKey.map Sum.inr,C.steps+3⟩
  else
    let K := copyFixed x.oldOwner
    ⟨some (.inl K.result),K.steps+3⟩

def endpointSpec {w own key prec page : ℕ} (col : Bool) (x : FramedEdge w own key prec page) :
    Option (Endpoint own page) :=
  if col then x.right.origin.pageKey.map Sum.inr else some (.inl x.oldOwner)

def endpointFee {w own key prec page : ℕ} (col : Bool) (x : FramedEdge w own key prec page) : ℕ :=
  if col then originFee key prec page x.right.origin.pageKey.isSome+3 else 3*own+4

theorem copied_endpoint_exact {w own key prec page : ℕ}
    (col : Bool) (x : FramedEdge w own key prec page) :
    copyEndpoint col x=⟨endpointSpec col x,endpointFee col x⟩ := by
  cases col <;> simp only [copyEndpoint,endpointSpec,endpointFee,Bool.false_eq_true,if_false,if_true,
    copy_fixed_exact,copy_origin_exact]

def readScopedEndpoint {w own key prec page : ℕ} (raw : Word w) (col : Bool) :
    List (FramedEdge w own key prec page) → Meter (Option (Endpoint own page))
  | [] => ⟨none,2⟩
  | x::xs =>
    let test := cmpAddr raw (frameRecordKey x)
    let touch := readFramedIncidence x
    if test.result then
      let E := copyEndpoint col x
      ⟨E.result,test.steps+touch.steps+E.steps+4⟩
    else
      let R := readScopedEndpoint raw col xs
      ⟨R.result,test.steps+touch.steps+R.steps+4⟩

def scannedFrameFee {w own key prec page : ℕ} (x : FramedEdge w own key prec page) :=
  10*w+5+framedIncidenceFee x+4

theorem real_frame_route_first_exact {w own key prec page : ℕ} (raw : Word w) (col : Bool)
    (x : FramedEdge w own key prec page) (before after : List (FramedEdge w own key prec page))
    (isKey : frameRecordKey x=raw) (prior : ∀ row∈before, frameRecordKey row≠raw) :
    readScopedEndpoint raw col (before++x::after)=
      ⟨endpointSpec col x,(before.map scannedFrameFee).sum+scannedFrameFee x+endpointFee col x⟩ := by
  induction before with
  | nil =>
    have t := cmpAddr_exact raw (frameRecordKey x)
    simp only [List.nil_append,readScopedEndpoint,if_pos (t.1.mpr isKey.symm),t.2,
      framed_incidence_row_exact,copied_endpoint_exact,List.map_nil,List.sum_nil,zero_add,scannedFrameFee]
    congr 1
    omega
  | cons a more ih =>
    have t := cmpAddr_exact raw (frameRecordKey a)
    have no : ¬(cmpAddr raw (frameRecordKey a)).result=true :=
      fun yes=>prior a List.mem_cons_self (t.1.mp yes).symm
    have rest := ih (fun b hb=>prior b (List.mem_cons_of_mem a hb))
    simp only [List.cons_append,readScopedEndpoint,if_neg no,t.2,framed_incidence_row_exact,rest,
      List.map_cons,List.sum_cons,scannedFrameFee]
    congr 1
    omega

theorem real_frame_route_hit {w own key prec page : ℕ} (raw : Word w) (col : Bool)
    (rows : List (FramedEdge w own key prec page)) (answer : Option (Endpoint own page))
    (here : ∃ row∈rows,frameRecordKey row=raw)
    (agree : ∀ row∈rows,frameRecordKey row=raw→endpointSpec col row=answer) :
    (readScopedEndpoint raw col rows).result=answer := by
  induction rows with
  | nil => obtain ⟨x,h,_⟩ := here; cases h
  | cons x xs ih =>
    have t := cmpAddr_exact raw (frameRecordKey x)
    by_cases same : frameRecordKey x=raw
    · rw [readScopedEndpoint,if_pos (t.1.mpr same.symm),copied_endpoint_exact]
      exact agree x List.mem_cons_self same
    · have no : ¬(cmpAddr raw (frameRecordKey x)).result=true := fun h=>same (t.1.mp h).symm
      rw [readScopedEndpoint,if_neg no]
      apply ih
      · obtain ⟨a,ha,eq⟩ := here
        rcases List.mem_cons.mp ha with h|h
        · subst a
          exact (same eq).elim
        · exact ⟨a,h,eq⟩
      · intro a ha eq
        exact agree a (List.mem_cons_of_mem x ha) eq

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
variable (cache : CachedParentFrames X.site)
local notation "Name" => (childKey T v X.birth.native.physical)

def currentEndpoint (e : v.child.host.Edge) (col : Bool) : Endpoint X.site.ownerWidth page :=
  if col then .inr (nativeColKey X.site (v.child.host.network.col e))
  else .inl (nativeRowKey X.site (v.child.host.network.row e))

theorem held_frame_book_is_current :
    cache.rows=(childOrder X.site).map (frameOf X.site) :=
  Option.some.inj (cache.exactRows.symm.trans (source_framed_in_child_order X.site))

theorem actual_frame_endpoint_is_paid (e : v.child.host.Edge) (col : Bool) :
    (readScopedEndpoint (Name e) col cache.rows).result=some (currentEndpoint X e col) := by
  rw [held_frame_book_is_current X cache]
  apply real_frame_route_hit
  · exact ⟨frameOf X.site e,
      List.mem_map.mpr ⟨e,(child_order_complete X.site).2 e,rfl⟩,frame_left_child_address X.site e⟩
  · intro row here h
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp here
    have relation : Name j=Name e := h
    have eq := child_key_injective T v X.birth.native.physical relation
    subst j
    have names := framed_edge_names_actual_endpoints X.site e
    cases col
    · simp only [currentEndpoint,endpointSpec,Bool.false_eq_true,if_false,names.1]
    · simp only [currentEndpoint,endpointSpec,if_true,names.2,Option.map_some]

#print axioms copied_endpoint_exact
#print axioms real_frame_route_first_exact
#print axioms real_frame_route_hit
#print axioms held_frame_book_is_current
#print axioms actual_frame_endpoint_is_paid
end
end J6R58RequestSource
