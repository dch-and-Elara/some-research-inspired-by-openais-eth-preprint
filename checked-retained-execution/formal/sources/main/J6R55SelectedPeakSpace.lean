import J6R55SelectedPeakWords
import J6R55SelectedPeakPlace
import J6R55SelectedPeakMountCore
import J6R54PeakInputReserve

/-! Named local selected snapshots under the real read-only owner
mount. During rekey the previous immutable payload is represented
once, and the separately copied prefix contributes address words.
This is a conservative reserve across named phases, not an assertion
that arbitrary raw objects are allocated or freed together. -/
namespace J6R55SelectedPeak
open scoped Polynomial
open J6R26DescriptorTree
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R30ProducedGateRegistry
open J6R33StatefulArithmeticPage J6R49SourceLayout J6R53OldOwner J6R54ExteriorOwner

set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 18400000

variable {f : ℤ[X]} {ell own gate key prec tw bw page next : ℕ}
local notation "D" => OwnerData gate key prec page
local notation "R" => RawRoster next gate key prec page
local notation "L" => PageBank f ell key prec tw bw page

def selectedReadBuffers (selected : List (Word own)) (old : List D) (stamp : Stamp key prec)
    (pages : List (Word page)) (destination : List (Word next)) : ℕ :=
  (selectedWordTape selected).length+(ownerTape old).length+
    (stamp.creator.bits++stamp.created.bits).length+(selectedWordTape pages).length+
    (selectedWordTape destination).length

def ownerMountPrefixBits (selected : List (Word own)) (old : List D) (stamp : Stamp key prec)
    (pages : List (Word page)) (destination : List (Word next)) (rowOutput : R)
    (freshPrefix indexedPrefix : ℕ) : ℕ :=
  selectedReadBuffers selected old stamp pages destination+
    (ownerTape ((writeFreshOwners (gate:=gate) stamp pages).result.take freshPrefix)).length+
    (selectedWordTape ((rowOutput.map RefRow.address).take indexedPrefix)).length

def ownerMountLocalReserve (selected : List (Word own)) (old : List D)
    (pages : List (Word page)) (destination : List (Word next)) : ℕ :=
  selected.length*own+(ownerTape old).length+(key+prec)+pages.length*page+destination.length*next+
    pages.length*freshPayloadWidth key prec page+destination.length*next

theorem actual_read_fields_have_the_named_bits
    (selected : List (Word own)) (old : List D) (stamp : Stamp key prec)
    (pages : List (Word page)) (destination : List (Word next)) :
    selectedReadBuffers selected old stamp pages destination=
      selected.length*own+(ownerTape old).length+(key+prec)+pages.length*page+destination.length*next := by
  simp only [selectedReadBuffers,selected_word_tape_width,List.length_append,
    stamp.creator.size,stamp.created.size]

theorem exact_writer_output_and_prefix_reserve
    (selected : List (Word own)) (old : List D) (stamp : Stamp key prec)
    (pages : List (Word page)) (destination : List (Word next)) (rows : R)
    (written : (writeMountedOwners stamp pages old destination).result=some rows) :
    (indexedOwnerTape rows).length=
      (ownerTape old).length+pages.length*freshPayloadWidth key prec page+destination.length*next ∧
    ∀ i j,ownerMountPrefixBits selected old stamp pages destination rows i j≤
      ownerMountLocalReserve selected old pages destination := by
  let fresh := writeFreshOwners (gate:=gate) stamp pages
  obtain ⟨names,contents⟩ := write_mount_returns_only_named_old_and_new_payloads
    stamp pages old destination rows written
  have count : rows.length=destination.length := by
    have e := congrArg List.length names
    rw [List.length_map] at e
    exact e
  constructor
  · rw [indexed_owner_tape_adds_address_width,contents,owner_tape_concatenates_actual_payloads,
      actual_fresh_tape_width,count]
  · intro i j
    have f : (ownerTape (fresh.result.take i)).length≤(ownerTape fresh.result).length :=
      J6R54PeakInput.encoded_take_le_full fresh.result ownerPayload i
    have s : (selectedWordTape ((rows.map RefRow.address).take j)).length≤
        (selectedWordTape (rows.map RefRow.address)).length :=
      J6R54PeakInput.encoded_take_le_full (rows.map RefRow.address) Word.bits j
    have freshWidth : (ownerTape fresh.result).length=pages.length*freshPayloadWidth key prec page :=
      actual_fresh_tape_width stamp pages
    rw [freshWidth] at f
    have outWidth : (selectedWordTape (rows.map RefRow.address)).length=destination.length*next := by
      rw [names,selected_word_tape_width]
    rw [outWidth] at s
    change selectedReadBuffers selected old stamp pages destination+
      (ownerTape (fresh.result.take i)).length+
        (selectedWordTape ((rows.map RefRow.address).take j)).length≤_
    rw [actual_read_fields_have_the_named_bits]
    exact Nat.add_le_add (Nat.add_le_add_left f _) s

theorem actual_owner_mount_observations_use_the_same_reserve
    (bank : L) (creator : Word key) (group : Word 6) (headers : List (OwnerGroup own))
    (rootRows : RawRoster own gate key prec page) (dest : Meter (List (Word next)))
    (old : List D) (stamp : Stamp key prec) (pages : List (Word page)) (rows : R)
    (fetchedOld : (gatherOwners rootRows (selectOwnerKeys group headers).result).result=some old)
    (fetchedPage : (readMountedOwners bank creator).result=some (stamp,pages))
    (success : (mountWords bank creator group headers rootRows dest).result=some rows) :
    let picked := (selectOwnerKeys group headers).result
    (indexedOwnerTape rows).length=
      (ownerTape old).length+pages.length*freshPayloadWidth key prec page+dest.result.length*next ∧
    ∀ i j,ownerMountPrefixBits picked old stamp pages dest.result rows i j≤
      ownerMountLocalReserve picked old pages dest.result := by
  have written := returning_mount_rows_leaves_exactly_the_paid_writer_output bank creator group headers
    rootRows dest stamp pages old fetchedOld fetchedPage rows success
  exact exact_writer_output_and_prefix_reserve (selectOwnerKeys group headers).result
    old stamp pages dest.result rows written

#print axioms actual_read_fields_have_the_named_bits
#print axioms exact_writer_output_and_prefix_reserve
#print axioms actual_owner_mount_observations_use_the_same_reserve
end J6R55SelectedPeak
