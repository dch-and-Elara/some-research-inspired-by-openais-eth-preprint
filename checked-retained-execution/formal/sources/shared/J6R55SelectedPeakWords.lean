import J6R53OldOwnerTape
import J6R51PeakSidecar

/-! Sizes of named owner payloads, not a model of encoded list spines
or arbitrary allocator fields. The gate projection accounts for
actual key and sign words, with explicit logical variant flags. -/
namespace J6R55SelectedPeak
open J6R26DescriptorTree
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R36ChildFramedRoute J6R51Peak J6R53OldOwner

set_option autoImplicit false
set_option maxRecDepth 3300
set_option maxHeartbeats 12200000

def selectedWordTape {w : ℕ} (xs : List (Word w)) : List Bool := xs.flatMap Word.bits

theorem selected_word_tape_width {w : ℕ} (xs : List (Word w)) :
    (selectedWordTape xs).length=xs.length*w := by
  induction xs with
  | nil => simp [selectedWordTape]
  | cons x xs ih =>
    change (x.bits++selectedWordTape xs).length=(xs.length+1)*w
    rw [List.length_append,x.size,ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]

def ownerGatePayload {w : ℕ} : CodeGate (Word w)→List Bool
  | .free => [false,false]
  | .equal keys => [false,true]++selectedWordTape keys
  | .clause keys signs => [true,false]++selectedWordTape keys++signs

def ownerPayload {gate key prec page : ℕ} (x : OwnerData gate key prec page) : List Bool :=
  originWords x.origin++[x.gateCode.isSome]++x.gateCode.toList.flatMap ownerGatePayload

def ownerTape {gate key prec page : ℕ} (xs : List (OwnerData gate key prec page)) : List Bool :=
  xs.flatMap ownerPayload

theorem owner_tape_concatenates_actual_payloads {gate key prec page : ℕ}
    (old fresh : List (OwnerData gate key prec page)) :
    (ownerTape (old++fresh)).length=(ownerTape old).length+(ownerTape fresh).length := by
  simp only [ownerTape,List.flatMap_append,List.length_append]

def freshPayloadWidth (key prec page : ℕ) : ℕ := key+prec+page+2

theorem fresh_owner_has_only_the_actual_page_and_stamp {gate key prec page : ℕ}
    (stamp : Stamp key prec) (keyWord : Word page) :
    (ownerPayload (freshOwnerData (gate:=gate) stamp keyWord)).length=freshPayloadWidth key prec page := by
  change (originWords (⟨stamp,some keyWord⟩ : Origin key prec page)++[false]++[]).length=_
  simp [origin_words_exact,freshPayloadWidth]
  omega

theorem actual_fresh_tape_width {gate key prec page : ℕ} (stamp : Stamp key prec) (pages : List (Word page)) :
    (ownerTape (writeFreshOwners (gate:=gate) stamp pages).result).length=
      pages.length*freshPayloadWidth key prec page := by
  rw [write_fresh_owners_exact]
  change (ownerTape (pages.map (freshOwnerData (gate:=gate) stamp))).length=_
  induction pages with
  | nil => simp [ownerTape]
  | cons k ks ih =>
    change (ownerPayload (freshOwnerData stamp k)++
      ownerTape (ks.map (freshOwnerData (gate:=gate) stamp))).length=(ks.length+1)*freshPayloadWidth key prec page
    rw [List.length_append,fresh_owner_has_only_the_actual_page_and_stamp,ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]

def indexedOwnerPayload {w gate key prec page : ℕ} (row : RefRow w (OwnerData gate key prec page)) : List Bool :=
  row.address.bits++ownerPayload row.payload

def indexedOwnerTape {w gate key prec page : ℕ} (rows : RawRoster w gate key prec page) : List Bool :=
  rows.flatMap indexedOwnerPayload

theorem indexed_owner_tape_adds_address_width {w gate key prec page : ℕ}
    (rows : RawRoster w gate key prec page) :
    (indexedOwnerTape rows).length=(ownerTape (rows.map RefRow.payload)).length+rows.length*w := by
  induction rows with
  | nil => simp [indexedOwnerTape,ownerTape]
  | cons x xs ih =>
    change ((x.address.bits++ownerPayload x.payload)++indexedOwnerTape xs).length=
      (ownerPayload x.payload++ownerTape (xs.map RefRow.payload)).length+(xs.length+1)*w
    rw [List.length_append,List.length_append,List.length_append,
      x.address.size,ih,Nat.add_mul,Nat.one_mul]
    omega

#print axioms selected_word_tape_width
#print axioms owner_tape_concatenates_actual_payloads
#print axioms fresh_owner_has_only_the_actual_page_and_stamp
#print axioms actual_fresh_tape_width
#print axioms indexed_owner_tape_adds_address_width
end J6R55SelectedPeak
