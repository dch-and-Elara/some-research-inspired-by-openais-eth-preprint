import J6R66BootPeakRequest
import J6R64BootSeatsAssembly
import J6R54PeakInputCore
import J6R55SelectedPeakWords
import J6R55SelectedPeakBootWriter

/-! Fields live at the source boundary during the genuine R55/R64
first-slot addon build and bank install. Separately paid owner input,
complete owner roster (including isolates), and actual port file
remain as independent operands. -/
namespace J6R66.BootPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6ActiveRun J6ActiveSchedule J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R26DescriptorTree J6R31RootResidentTables J6R32ChildResidentTransfer
open J6R34RootAtlas J6R36ChildFramedRoute J6R48GeneratedAddons J6R48RawRoute
open J6R49SourceLayout J6R50SourceProducer J6R55TerminalOrigin J6R58BootScope J6R53OldOwner
open J6R10Repack P11FullPacking J6R9PacketScopes J6OrientedHost J6R20Ancestor
open J6R64.BootSeats J6R54PeakInput J6R55SelectedPeak J6R51Peak J6R53PeakAddon J6R52CacheWhole
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4700
set_option Elab.async false

theorem bitSize_le {A : Type*} (encode : A→List Bool) (rows : List A) (width : ℕ)
    (size : ∀ x∈rows,(encode x).length≤width) :
    bitSize encode rows≤rows.length*width := by
  induction rows with
  | nil => simp only [bitSize,List.flatMap_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons x xs ih =>
    change (encode x++xs.flatMap encode).length≤(xs.length+1)*width
    rw [List.length_append,Nat.add_mul,Nat.one_mul,Nat.add_comm (xs.length*width)]
    exact Nat.add_le_add (size x List.mem_cons_self)
      (ih (fun y h=>size y (List.mem_cons_of_mem x h)))

def bootQueryBits {w own : ℕ} (x : RefRow w (Word own×Word w×Bool)) : List Bool :=
  x.address.bits++x.payload.1.bits++x.payload.2.1.bits++[x.payload.2.2]

theorem boot_query_record_width {w own : ℕ} (x : RefRow w (Word own×Word w×Bool)) :
    (bootQueryBits x).length=w+own+w+1 := by
  simp only [bootQueryBits,List.length_append,x.address.size,x.payload.1.size,x.payload.2.1.size,
    List.length_cons,List.length_nil]

def projectedOriginBits {own key prec page : ℕ}
    (x : RefRow own (Word own×Origin key prec page)) : List Bool :=
  x.address.bits++x.payload.1.bits++originWords x.payload.2

theorem projected_origin_table_bound {own gate key prec page : ℕ}
    (R : RawRoster own gate key prec page) :
    bitSize projectedOriginBits (projectOriginTape R).result≤
      R.length*(2*own+key+prec+page+1) := by
  rw [project_origin_tape_exact]
  dsimp only
  have b := bitSize_le projectedOriginBits (R.map originRow) (2*own+key+prec+page+1) (by
    intro x _
    simp only [projectedOriginBits,List.length_append,x.address.size,x.payload.1.size,origin_words_exact]
    cases x.payload.2.pageKey.isSome <;> simp <;> omega)
  rw [List.length_map] at b
  exact b

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page own gw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (input : Meter (OccurrenceInput T v key prec tw bw page))
variable {name : v.parent.host.Row⊕v.parent.host.Col→Word own}
variable {value : v.parent.host.Row⊕v.parent.host.Col→OwnerData gw key prec page}
variable {tags : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (source : Meter (CompleteRoster name value))
variable (tagLaw : ∀ x,(value x).origin=tags x) (inj : Function.Injective name)
variable (pairOrder : input.result.native.result.physical.order=pairedPorts input.result.geometry.edges)
variable (ownerTape : Meter (OwnerTape input.result name)) (fallback : Addon own (dim v) key prec page)
local notation "N" => (2*v.parent.edges)

def canonicalInitReserve (birthPort : ℕ) : ℕ :=
  (indexedOwnerTape source.result.raw).length+source.result.raw.length*(2*own+key+prec+page+1)+
  N*(input.result.port+own+input.result.port+1)+N*(input.result.port+dim v+page+12)+
  (input.result.native.result.physical.raw.flatMap physicalPortWords).length+
  N*(2*addonCap own (dim v) key prec page+birthPort)

def canonicalInitCut (state : StoredSite T v key prec tw bw page)
    (originPrefix queryPrefix seatPrefix rawPrefix indexedPrefix : ℕ) : ℕ :=
  let resident := installResidentBank state
  (indexedOwnerTape source.result.raw).length+
  bitSize projectedOriginBits ((projectOriginTape source.result.raw).result.take originPrefix)+
  bitSize bootQueryBits (ownerTape.result.rows.take queryPrefix)+
  bitSize (fun row=>row.address.bits++physicalSeatBits row.payload)
    ((canonicalSeatBank input.result).result.take seatPrefix)+
  (input.result.native.result.physical.raw.flatMap physicalPortWords).length+
  bitSize addonWords (state.site.input.take rawPrefix)+
  bitSize indexedAddonBits (resident.result.rows.take indexedPrefix)

theorem canonical_first_boot_buffers_are_bounded
    (originPrefix queryPrefix seatPrefix rawPrefix indexedPrefix : ℕ) :
    let state := (boundedAssembly input source tagLaw inj pairOrder ownerTape fallback).result
    canonicalInitCut input source ownerTape state originPrefix queryPrefix seatPrefix rawPrefix indexedPrefix≤
      canonicalInitReserve input source state.birth.port := by
  let I := input.result
  let state := (boundedAssembly input source tagLaw inj pairOrder ownerTape fallback).result
  let resident := (installResidentBank state).result
  have query : bitSize bootQueryBits ownerTape.result.rows=N*((I).port+own+(I).port+1) := by
    rw [bitSize_exact _ _ _ boot_query_record_width,
      (query_tape_exactly_native_halfports I name ownerTape.result).1]
  have seat : bitSize (fun row=>row.address.bits++physicalSeatBits row.payload)
      (canonicalSeatBank I).result=N*((I).port+dim v+page+12) := by
    rw [bitSize_exact _ _ ((I).port+dim v+page+12)
        (fun row=>by
          rw [List.length_append,row.address.size,physical_seat_bits_exact]
          omega),
      (canonical_full_native_seat_table I pairOrder).1]
  have ow : state.site.ownerWidth=own := rfl
  have raw : bitSize addonWords state.site.input≤N*addonCap own (dim v) key prec page := by
    have checked := (stored_raw_is_bounded_and_counts_true_parent_halves state).2.2
    rw [ow] at checked
    exact checked
  have idx := actual_sidecar_extra_bits_are_its_address_lane resident
  change bitSize indexedAddonBits resident.rows=bitSize addonWords state.site.input+N*state.birth.port at idx
  have qo := (bitSize_take projectedOriginBits (projectOriginTape source.result.raw).result originPrefix).trans
    (projected_origin_table_bound source.result.raw)
  have qq := (bitSize_take bootQueryBits ownerTape.result.rows queryPrefix).trans_eq query
  have qs := (bitSize_take (fun row=>row.address.bits++physicalSeatBits row.payload)
    (canonicalSeatBank I).result seatPrefix).trans_eq seat
  have qr := (bitSize_take addonWords state.site.input rawPrefix).trans raw
  have qi := (bitSize_take indexedAddonBits resident.rows indexedPrefix).trans_eq idx

  have pre := Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left qo
      (indexedOwnerTape source.result.raw).length) qq) qs)
    (input.result.native.result.physical.raw.flatMap physicalPortWords).length
  have two := Nat.add_le_add qr (qi.trans (Nat.add_le_add_right raw (N*state.birth.port)))
  calc
    _ = _ := Nat.add_assoc _ _ _
    _ ≤ _ := Nat.add_le_add pre two
    _ = _ := by unfold canonicalInitReserve; ring

#print axioms bitSize_le
#print axioms projected_origin_table_bound
#print axioms canonicalInitReserve
#print axioms canonical_first_boot_buffers_are_bounded
end
end J6R66.BootPeak
