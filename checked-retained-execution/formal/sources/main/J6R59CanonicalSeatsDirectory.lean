import J6R59CanonicalSeatsCore

/-! The canonical rows really replace the seat rail of the local
directory. Owners and physical query words are unchanged. There is
one record per current physical edge, not one per half-port, and the
actual sidecar lookup bound no longer uses the offered U.rows length. -/
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
open J6R51ParentFrames J6R52CacheSource J6R58RequestSource J6R25PreparedSupply J6R53OldOwner
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4800
set_option maxHeartbeats 24000000
set_option Elab.async false

def recordBitCount {w a p : ℕ} (r : RefRow w (SeatField a p)) : ℕ :=
  r.address.bits.length+r.payload.slot.bits.length+r.payload.page.bits.length+
    r.payload.rowGroup.bits.length+r.payload.colGroup.bits.length

theorem fixed_record_bit_count {w a p : ℕ} (r : RefRow w (SeatField a p)) :
    recordBitCount r=w+a+p+12 := by
  unfold recordBitCount
  rw [r.address.size,r.payload.slot.size,r.payload.page.size,r.payload.rowGroup.size,r.payload.colGroup.size]

theorem fixed_bit_count_sum {w a p : ℕ} (l : List (RefRow w (SeatField a p))) :
    (l.map recordBitCount).sum=(w+a+p+12)*l.length := by
  induction l with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,fixed_record_bit_count,ih,Nat.mul_succ]
    omega

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page gwidth : ℕ} {cfg : RootBounds s C f}
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
local notation "ow" => (1+(X.site.ownerWidth+page))
local notation "Order" => (childOrder X.site)

variable (B : PayloadShell R)

def canonicalDirectorySeats : Meter (List (RefRow X.birth.port (SeatField (dim nx) page))) :=
  let paid := canonicalBank X cache R
  ⟨reindexSeatWidth B.width paid.result,paid.steps⟩

theorem canonical_directory_seats_exact :
    let made := canonicalDirectorySeats X cache R B
    made.result=(Order).map
      (fun e=>⟨edKey e,physicalSeatField (layout T nx) (axis T nx) (shellPageWord R B) e⟩) ∧
      made.steps=(frameKeys cache.rows).steps+8+(3*X.birth.port+3*(A+K)+55)*v.child.edges := by
  have w := canonical_bank_exact X cache R
  refine ⟨?_,w.2⟩
  change reindexSeatWidth B.width (canonicalBank X cache R).result=_
  rw [w.1]
  exact reindex_physical_seat_rows (layout T nx) (axis T nx) (childPageKey (q-A))
    edKey (Order) B.width

theorem physical_table_count_distinct_and_bits :
    let D := (canonicalDirectorySeats X cache R B).result
    D.length=v.child.edges ∧ (D.map RefRow.address).Nodup ∧
      (D.map recordBitCount).sum=(X.birth.port+dim nx+page+12)*v.child.edges := by
  have shapes := (canonical_directory_seats_exact X cache R B).1
  have size : (canonicalDirectorySeats X cache R B).result.length=v.child.edges := by
    rw [shapes,List.length_map,true_order_has_one_entry_per_edge X]
  refine ⟨size,?_,?_⟩
  · change ((canonicalDirectorySeats X cache R B).result.map RefRow.address).Nodup
    rw [shapes,List.map_map]
    exact (child_order_complete X.site).1.map (child_key_injective T v X.birth.native.physical)
  · change ((canonicalDirectorySeats X cache R B).result.map recordBitCount).sum=_
    rw [fixed_bit_count_sum,size]

theorem actual_physical_key_has_exactly_one_seat (e : v.child.host.Edge) :
    let bank := (canonicalDirectorySeats X cache R B).result
    let actual := physicalSeatField (layout T nx) (axis T nx) (shellPageWord R B) e
    (⟨edKey e,actual⟩ : RefRow X.birth.port (SeatField (dim nx) page))∈bank ∧
      ∀ row ∈ bank, row.address = edKey e → row.payload = actual := by
  dsimp only
  rw [(canonical_directory_seats_exact X cache R B).1]
  refine ⟨List.mem_map.mpr ⟨e,(child_order_complete X.site).2 e,rfl⟩,?_⟩
  intro r hit addr
  obtain ⟨earlier,_,rfl⟩ := List.mem_map.mp hit
  have s := child_key_injective T v X.birth.native.physical addr
  rw [s]

variable (port : PaidPortIndex X)
variable (gates : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gwidth)))
variable (source : CompleteRoster X.site.oldKey (parentData X gates))
variable (H : ParentOwnerHeaders X.site) (inj : Function.Injective X.site.oldKey)
local notation "OwnerBank" => (buildOriginBank X gates source H inj)
local notation "Query" => (queryActualPort X cache port)
local notation "SeatBank" => (canonicalDirectorySeats X cache R B)

theorem canonical_native_table_no_miss :
    NativeTables X.childOrigins (nameCurrentOwner X) (shellPageWord R B)
      (OwnerBank).result (SeatBank).result Query := by
  have old := generated_native_routes_all_hit X cache port R gates source H inj B
  refine ⟨old.side_matches,old.owner_hit,old.owner_unique,?_,?_⟩
  · intro h
    rw [(actual_query_is_from_live_chart X cache port h).1]
    exact (actual_physical_key_has_exactly_one_seat X cache R B (edge h)).1
  · intro h row hit hAddr
    rw [(actual_query_is_from_live_chart X cache port h).1] at hAddr
    exact (actual_physical_key_has_exactly_one_seat X cache R B (edge h)).2 row hit hAddr

def canonicalNextDirectory (fallback : Addon ow (dim nx) key prec page) : Meter (DirectorySeed R B) :=
  let O := buildOriginBank X gates source H inj
  let D := canonicalDirectorySeats X cache R B
  ⟨⟨ow,X.birth.port,ow,nameCurrentOwner X,O.result,D.result,queryActualPort X cache port,fallback,
    canonical_native_table_no_miss X cache R B port gates source H inj⟩,O.steps+D.steps+4⟩

theorem exact_canonical_directory_fee
    (fallback : Addon ow (dim nx) key prec page) :
    (canonicalNextDirectory X cache R B port gates source H inj fallback).steps =
      (OwnerBank).steps+(frameKeys cache.rows).steps+12+
      (3*X.birth.port+3*(A+K)+55)*v.child.edges := by
  change (OwnerBank).steps+(SeatBank).steps+4=_
  rw [(canonical_directory_seats_exact X cache R B).2]
  omega

theorem original_sidecar_answer_on_canonical_bank (h : Port v.child.host.Edge) :
    (residentRead (OwnerBank).result (SeatBank).result (Query h)).result =
      (residentRead (OwnerBank).result (directorySeatRows R B) (Query h)).result := by
  rw [no_raw_row_miss _ _ _ _ _ _ (canonical_native_table_no_miss X cache R B port gates source H inj) h,
    no_raw_row_miss _ _ _ _ _ _ (generated_native_routes_all_hit X cache port R gates source H inj B) h]

theorem actual_sidecar_lookup_bound_uses_physical_edges (h : Port v.child.host.Edge) :
    (residentRead (OwnerBank).result (SeatBank).result (Query h)).steps≤
      (Query h).steps+locateFee ow (OwnerBank).result.length+
        locateFee X.birth.port v.child.edges+8 := by
  have privateBound := resident_read_bound (OwnerBank).result (SeatBank).result (Query h)
  rw [(physical_table_count_distinct_and_bits X cache R B).1] at privateBound
  exact privateBound

#print axioms fixed_record_bit_count
#print axioms fixed_bit_count_sum
#print axioms canonical_directory_seats_exact
#print axioms physical_table_count_distinct_and_bits
#print axioms actual_physical_key_has_exactly_one_seat
#print axioms canonical_native_table_no_miss
#print axioms canonicalNextDirectory
#print axioms exact_canonical_directory_fee
#print axioms original_sidecar_answer_on_canonical_bank
#print axioms actual_sidecar_lookup_bound_uses_physical_edges
end
end J6R59CanonicalSeats
