import J6R64BootSeatsNative
import J6R58BootScopeReads

/-! The independent fixed-width owner-query tape carries only genuinely
indexed owner keys, true side and canonical native address. An old
BootPortWords or its arbitrary seats list is not in this API. -/
namespace J6R64.BootSeats
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6ActiveRun J6ActiveSchedule J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R26DescriptorTree J6R31RootResidentTables J6R32ChildResidentTransfer
open J6R34RootAtlas J6R36ChildFramedRoute J6R48GeneratedAddons J6R48RawRoute
open J6R49SourceLayout J6R50SourceProducer J6R55TerminalOrigin J6R58BootScope J6R53OldOwner
open J6R10Repack P11FullPacking J6R9PacketScopes J6OrientedHost J6R20Ancestor
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 5000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page own : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (I : OccurrenceInput T v key prec tw bw page)
variable (name : v.parent.host.Row⊕v.parent.host.Col→Word own)
local notation "Physical" => (I.native.result.physical)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.parent.depth)
local notation "Half" => (Port v.parent.host.Edge)
local notation "K" => (realHalfKey I)

def trueQuery (h : Half) : Word own × Word I.port × Bool :=
  (name (owner v.parent.host.network h),K h,side h)

structure OwnerTape where
  rows : List (RefRow I.port (Word own × Word I.port × Bool))
  exact : rows=(Physical).order.map (fun h=>⟨K h,trueQuery I name h⟩)

variable (O : OwnerTape I name)

theorem query_tape_exactly_native_halfports :
    O.rows.length=2*v.parent.edges ∧ (O.rows.map RefRow.address).Nodup := by
  rw [O.exact,List.length_map,List.map_map]
  exact ⟨actual_native_halfport_count I,(Physical).nodup.map (real_native_half_keys_are_distinct I)⟩

theorem checked_owner_lookup_hit (h : Half) :
    (locate (K h) O.rows).result=some (trueQuery I name h) := by
  rw [O.exact]
  apply locate_hit
  · exact List.mem_map.mpr ⟨h,(Physical).complete h,rfl⟩
  · intro row inside eq
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp inside
    have zi := real_native_half_keys_are_distinct I eq
    rw [zi]

theorem paid_owner_for_current_halfport (h : Half) :
    (readBootQueryRow O.rows (K h)).result=trueQuery I name h ∧
      (readBootQueryRow O.rows (K h)).steps ≤
        locateFee I.port (2*v.parent.edges)+6*I.port+3*own+9 := by
  have hq := actual_boot_query_row_and_width O.rows (K h) _ (checked_owner_lookup_hit I name O h)
  have b := (query_tape_exactly_native_halfports I name O).1
  refine ⟨hq.1,?_⟩
  rw [b] at hq
  omega

/-- The caller provides the independently paid owner-word file, not
a seat chart. Its paid formation is added once via the actual seat
provider Meter that assembleOriginSite uses once. The per-port
query keeps the already formed file by reference. -/
def bootProvider
    (paired : (Physical).order=pairedPorts I.geometry.edges)
    (made : Meter (OwnerTape I name))
    (backup : Addon own (dim v) key prec page) : BootPortWords I name where
  seatWidth := I.port
  seats :=
    let seat := canonicalSeatBank I
    ⟨seat.result,made.steps+seat.steps+3⟩
  queries h := readBootQueryRow made.result.rows (K h)
  ownerQuery h := congrArg Prod.fst (paid_owner_for_current_halfport I name made.result h).1
  sideExact h := congrArg (fun x=>x.2.2) (paid_owner_for_current_halfport I name made.result h).1
  seatHit h := by
    change (⟨(readBootQueryRow made.result.rows (K h)).result.2.1,
      rawSeat (T:=T) (v:=v) (occurrencePageWord I) h⟩ : RefRow I.port _)
        ∈(canonicalSeatBank I).result
    rw [(paid_owner_for_current_halfport I name made.result h).1]
    exact (real_native_seat_is_present_and_unique I paired h).1
  seatUnique h x hm eq := by
    change x.address=(readBootQueryRow made.result.rows (K h)).result.2.1 at eq
    rw [(paid_owner_for_current_halfport I name made.result h).1] at eq
    exact (real_native_seat_is_present_and_unique I paired h).2 x hm eq
  fallback := backup

theorem canonical_boot_provider_counts_and_fee
    (pairedChart : I.native.result.physical.order=pairedPorts I.geometry.edges)
    (madeOwner : Meter (OwnerTape I name)) (fallback : Addon own (dim v) key prec page) :
    let D := bootProvider I name pairedChart madeOwner fallback
    D.seats.result.length=2*v.parent.edges ∧
      (D.seats.result.map RefRow.address).Nodup ∧
      (D.seats.result.map lookupRecordBits).sum=(I.port+dim v+page+12)*(2*v.parent.edges) ∧
      D.seats.steps=madeOwner.steps+6+pairStride I.port (dim v) page*I.geometry.edges.length+3 := by
  obtain ⟨len,unique,bits⟩ := canonical_full_native_seat_table I pairedChart
  refine ⟨len,unique,bits,?_⟩
  change madeOwner.steps+(canonicalSeatBank I).steps+3=_
  rw [(paired_seats_emit_exact_rows I pairedChart).2]
  omega

theorem old_and_bounded_boot_addon_agree
    (pairedChart : I.native.result.physical.order=pairedPorts I.geometry.edges)
    (madeOwner : Meter (OwnerTape I name)) (fallback : Addon own (dim v) key prec page)
    {gw : ℕ}
    {value : v.parent.host.Row⊕v.parent.host.Col→OwnerData gw key prec page}
    (R : CompleteRoster name value) {tag : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
    (tags : ∀ x,(value x).origin=tag x) (inj : Function.Injective name)
    (old : BootPortWords I name) (h : Half) :
    (readBootAddon (bootProvider I name pairedChart madeOwner fallback) R h).result=
      (readBootAddon old R h).result :=
  (read_boot_addon_exact _ R tags inj h).trans (read_boot_addon_exact old R tags inj h).symm

#print axioms query_tape_exactly_native_halfports
#print axioms checked_owner_lookup_hit
#print axioms paid_owner_for_current_halfport
#print axioms bootProvider
#print axioms canonical_boot_provider_counts_and_fee
#print axioms old_and_bounded_boot_addon_agree
end
end J6R64.BootSeats
