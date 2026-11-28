import J6R58RequestSourceDirectory
import J6R49SourceLayoutOrder

/-! Use the exact same actual selected replay. Its seat payloads
and its paid cached frame keys have one physical order, with each
actual child edge appearing once. An external selected lookup bank
is neither scanned nor copied when this canonical bank is written. -/
namespace J6R59CanonicalSeats
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open P11FullPacking J6R9PacketScopes J6R10Repack J6R12CollisionEdges
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R33GeneratedChildSite
open J6R34ChildPath J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R50SourceProducer J6R51Online J6R52Dispatch
open J6R21Ancestor J6R36ChildFramedRoute J6R34RootAtlas J6R20Ancestor
open J6R51ParentFrames J6R52CacheSource J6R58RequestSource J6R25PreparedSupply
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4300
set_option maxHeartbeats 18000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
variable (cache : CachedParentFrames X.site)
variable {u : (Plan sel).Slot v.child} {q : ℕ} {U : ExplicitSelectedWords X.site u q}
variable (R : Replayed X.site u q U)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
local notation "K" => ((q-A)+13*A)
local notation "nx" => (successorTicket v u)
local notation "edKey" => (childKey T v X.birth.native.physical)
local notation "Order" => (childOrder X.site)

theorem true_order_has_one_entry_per_edge : (Order).length=v.child.edges := by
  unfold childOrder
  rw [List.length_ofFn]

theorem frame_key_read_in_actual_physical_order :
    let keys := frameKeys cache.rows
    keys.result=(Order).map edKey ∧
      keys.result=(selectedEdgeBook X.birth.native.gWord X.birth.native.physical.raw).result ∧
      keys.result.Nodup ∧
      keys.steps=3+(cache.rows.map (fun x=>3*X.birth.port+5+framedIncidenceFee x)).sum := by
  have out := frame_keys_exact cache.rows
  have hMap : cache.rows.map frameRecordKey=(Order).map edKey := by
    rw [held_frame_book_is_current X cache,List.map_map]
    apply List.map_congr_left
    intro e _
    exact frame_left_child_address X.site e
  have phys := (exact_child_edge_book T v X.birth.native).1
  have eq : (Order).map edKey=(selectedEdgeBook X.birth.native.gWord X.birth.native.physical.raw).result := by
    rw [phys,childOrder,List.map_ofFn]
    rfl
  have nd : (frameKeys cache.rows).result.Nodup := by
    rw [out]
    dsimp only
    rw [hMap]
    exact (child_order_complete X.site).1.map (child_key_injective T v X.birth.native.physical)
  exact ⟨(congrArg Meter.result out).trans hMap,
    (congrArg Meter.result out).trans (hMap.trans eq),nd,congrArg Meter.steps out⟩

abbrev expectedSeat (e : v.child.host.Edge) : SeatField A K :=
  physicalSeatField (layout T nx) (axis T nx) (childPageKey (q-A)) e

include R in
theorem selected_payloads_are_in_the_same_physical_order :
    R.resident.seats=(Order).map (expectedSeat (T:=T) (v:=v) (u:=u) (q:=q)) := by
  exact R.certificate.seats.trans (congrArg (fun l=>l.map
    (expectedSeat (T:=T) (v:=v) (u:=u) (q:=q))) R.orderEq)

def writeCanonical (R : Replayed X.site u q U) :
    Meter (Option (List (RefRow X.birth.port (SeatField A K)))) :=
  let keys := frameKeys cache.rows
  let bank := pairKeyedSeats keys.result R.resident.seats
  ⟨bank.result,keys.steps+bank.steps+4⟩

theorem actual_written_seats_and_fee :
    writeCanonical X cache R=
      ⟨some ((Order).map (fun e=>⟨edKey e,expectedSeat (T:=T) (v:=v) (u:=u) (q:=q) e⟩)),
        (frameKeys cache.rows).steps+8+(3*X.birth.port+3*(A+K)+55)*v.child.edges⟩ := by
  have keys := (frame_key_read_in_actual_physical_order X cache).1
  have seats := selected_payloads_are_in_the_same_physical_order X R
  have pair := paired_seats_exact (Order) edKey (expectedSeat (T:=T) (v:=v) (u:=u) (q:=q))
  rw [true_order_has_one_entry_per_edge X] at pair
  unfold writeCanonical
  dsimp only
  rw [keys,seats,pair]
  dsimp only
  congr 1
  omega

def canonicalBank : Meter (List (RefRow X.birth.port (SeatField A K))) :=
  unwrapSuccess (writeCanonical X cache R) (by rw [actual_written_seats_and_fee X cache R]; rfl)

theorem canonical_bank_exact :
    let M := canonicalBank X cache R
    M.result=(Order).map (fun e=>⟨edKey e,expectedSeat (T:=T) (v:=v) (u:=u) (q:=q) e⟩) ∧
      M.steps=(frameKeys cache.rows).steps+8+(3*X.birth.port+3*(A+K)+55)*v.child.edges := by
  let w := writeCanonical X cache R
  have h := actual_written_seats_and_fee X cache R
  have eq (good : w.result.isSome) := unwrap_success_exact w good _ (congrArg Meter.result h)
  have yes : w.result.isSome := by
    change (writeCanonical X cache R).result.isSome
    rw [h]
    rfl
  refine ⟨congrArg Meter.result (eq yes),?_⟩
  change w.steps=_
  exact congrArg Meter.steps h

theorem bank_exact_size_and_distinct :
    let M := canonicalBank X cache R
    M.result.length=v.child.edges ∧ (M.result.map RefRow.address).Nodup := by
  dsimp only
  rw [(canonical_bank_exact X cache R).1,List.length_map,List.map_map]
  exact ⟨true_order_has_one_entry_per_edge X,
    (child_order_complete X.site).1.map (child_key_injective T v X.birth.native.physical)⟩

#print axioms true_order_has_one_entry_per_edge
#print axioms frame_key_read_in_actual_physical_order
#print axioms selected_payloads_are_in_the_same_physical_order
#print axioms actual_written_seats_and_fee
#print axioms canonical_bank_exact
#print axioms bank_exact_size_and_distinct
end
end J6R59CanonicalSeats
