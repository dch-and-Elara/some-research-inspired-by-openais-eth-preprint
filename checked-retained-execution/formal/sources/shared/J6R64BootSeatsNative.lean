import J6R64BootSeatsRaw
import J6R48RawRouteOccurrence
import J6R58BootScopeWriter

/-! Form the lookup table from the same actual new physical file and
receiving-seat words. Width transport changes no bits. No raw
BootPortWords seat table is an input. -/
namespace J6R64.BootSeats
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6ActiveRun J6ActiveSchedule J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R26DescriptorTree J6R31RootResidentTables J6R32ChildResidentTransfer
open J6R34RootAtlas J6R34ChildPath J6R36ChildFramedRoute J6R48GeneratedAddons J6R48RawRoute
open J6R49SourceLayout J6R55TerminalOrigin J6R58BootScope
open J6R10Repack P11FullPacking J6R9PacketScopes J6OrientedHost J6R20Ancestor J6R25PreparedSupply J6R30ProducedGateRegistry
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 4900
set_option Elab.async false

def reindexSeats {a b c : ℕ} (same : b=c) (rs : List (SeatField a b)) :
    List (SeatField a c) := same ▸ rs

theorem reindex_exact_seats {E L R : Type} {N : Network E L R} {a b c : ℕ}
    (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (code : Page a P.copies (Fin 64)→Word b)
    (es : List E) (same : b=c) :
    reindexSeats same (es.map (physicalSeatField P i code))=
      es.map (physicalSeatField P i (fun p=>(same ▸ code p : Word c))) := by
  cases same
  rfl

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (I : OccurrenceInput T v key prec tw bw page)
local notation "Physical" => (I.native.result.physical)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.parent.depth)
local notation "Half" => (Port v.parent.host.Edge)

def realHalfKey (h : Half) : Word I.port := ((Physical).record h).address

def expectedRow (h : Half) : RefRow I.port (SeatField (dim v) page) :=
  ⟨realHalfKey I h,rawSeat (T:=T) (v:=v) (occurrencePageWord I) h⟩

def canonicalSeatBank : Meter (List (RefRow I.port (SeatField (dim v) page))) :=
  let Q := writePairs (Physical).raw (reindexSeats I.width I.physical.result.seats)
  ⟨Q.result.getD [],Q.steps+3⟩

theorem checked_receiving_seat_bank :
    reindexSeats I.width I.physical.result.seats=
      I.geometry.edges.map (physicalSeatField (layout T v) (axis T v) (occurrencePageWord I)) := by
  rw [I.geometry.seats]
  exact reindex_exact_seats (packing sel (ticketReady T v)) (centerIndex (ticketReady T v) v.centerAt)
    (childPageKey (I.q-A)) I.geometry.edges I.width

theorem real_native_half_keys_are_distinct : Function.Injective (realHalfKey I) :=
  (Physical).distinct

theorem same_born_key_bytes (h : Half) :
    (realHalfKey I h).bits=((compileOccurrence I).native.physical.record h).address.bits :=
  (congrArg (fun X : Σ w,PhysicalFile T v w=>(X.2.record h).address.bits)
    (compileOccurrence_native_file I)).symm

theorem paired_seats_emit_exact_rows
    (order : (Physical).order=pairedPorts I.geometry.edges) :
    (canonicalSeatBank I).result=(Physical).order.map (expectedRow I) ∧
    (canonicalSeatBank I).steps=6+pairStride I.port (dim v) page*I.geometry.edges.length := by
  have R := write_pairs_exact I.geometry.edges (Physical).record
    (physicalSeatField (layout T v) (axis T v) (occurrencePageWord I))
  unfold canonicalSeatBank
  rw [checked_receiving_seat_bank I,(Physical).source,order,R]
  refine ⟨rfl,?_⟩
  change (3+pairStride I.port (dim v) page*I.geometry.edges.length)+3=
    6+pairStride I.port (dim v) page*I.geometry.edges.length
  omega

theorem actual_native_halfport_count :
    (Physical).order.length=2*v.parent.edges := by
  have p := congrArg (fun Y : Σ w,PhysicalFile T v w => Y.2.order.length) (compileOccurrence_native_file I)
  exact p.symm.trans (boot_native_half_port_count I)

theorem canonical_full_native_seat_table
    (order : (Physical).order=pairedPorts I.geometry.edges) :
    let rows := (canonicalSeatBank I).result
    rows.length=2*v.parent.edges ∧
      (rows.map RefRow.address).Nodup ∧
      (rows.map lookupRecordBits).sum=(I.port+dim v+page+12)*(2*v.parent.edges) := by
  dsimp only
  have exactRows := (paired_seats_emit_exact_rows I order).1
  have length : (canonicalSeatBank I).result.length=2*v.parent.edges := by
    rw [exactRows,List.length_map,actual_native_halfport_count I]
  refine ⟨length,?_,?_⟩
  · rw [exactRows,List.map_map]
    exact (Physical).nodup.map (real_native_half_keys_are_distinct I)
  · rw [serialized_lookup_table_size,length]

theorem real_native_seat_is_present_and_unique
    (order : (Physical).order=pairedPorts I.geometry.edges) (h : Half) :
    let rows := (canonicalSeatBank I).result
    expectedRow I h ∈ rows ∧
      ∀ row ∈ rows,row.address=realHalfKey I h → row.payload=(expectedRow I h).payload := by
  dsimp only
  rw [(paired_seats_emit_exact_rows I order).1]
  refine ⟨List.mem_map.mpr ⟨h,(Physical).complete h,rfl⟩,?_⟩
  intro row inside eq
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp inside
  have here := real_native_half_keys_are_distinct I eq
  rw [here]

#print axioms reindex_exact_seats
#print axioms checked_receiving_seat_bank
#print axioms canonicalSeatBank
#print axioms same_born_key_bytes
#print axioms paired_seats_emit_exact_rows
#print axioms actual_native_halfport_count
#print axioms canonical_full_native_seat_table
#print axioms real_native_seat_is_present_and_unique
end
end J6R64.BootSeats
