import J6R54ExteriorOwnerWords

/-! The post-read ABI of the actual owner mount. It takes only the
completed old payloads, the stamp/Page keys and the destination tape.
The bank, complete source roster and selector headers are NOT
parameters of this continuation. This is a scope contract for the
source program, not a theorem about reference reclamation by Lean. -/
namespace J6R55SelectedPeak
open scoped Polynomial
open J6R26DescriptorTree
open AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R49SourceLayout
open J6R53OldOwner J6R54ExteriorOwner

set_option autoImplicit false
set_option maxRecDepth 3450
set_option maxHeartbeats 14500000

variable {f : ℤ[X]} {ell own gate key prec tw bw page next : ℕ}
local notation "D" => OwnerData gate key prec page
local notation "R" => RawRoster next gate key prec page
local notation "L" => PageBank f ell key prec tw bw page

structure OwnerWriterInput (gate key prec page next : ℕ) where
  stamp : Stamp key prec
  pages : List (Word page)
  old : List (OwnerData gate key prec page)
  dest : Meter (List (Word next))

def resumeOwnerMountAfterReads (readFee : ℕ) (inputs : OwnerWriterInput gate key prec page next) :
    Meter (Option R) :=
  let done := writeMountedOwners inputs.stamp inputs.pages inputs.old inputs.dest.result
  ⟨done.result,readFee+inputs.dest.steps+done.steps+8⟩

theorem original_owner_mount_uses_exact_bank_free_write_phase
    (bank : L) (creator : Word key) (group : Word 6)
    (headers : List (OwnerGroup own)) (rootRows : RawRoster own gate key prec page)
    (destination : Meter (List (Word next))) (s : Stamp key prec) (pages : List (Word page)) (old : List D)
    (copied : (gatherOwners rootRows (selectOwnerKeys group headers).result).result=some old)
    (readPage : (readMountedOwners bank creator).result=some (s,pages)) :
    let sel := selectOwnerKeys group headers
    let readFee := sel.steps+(gatherOwners rootRows sel.result).steps+(readMountedOwners bank creator).steps
    mountWords bank creator group headers rootRows destination=
      resumeOwnerMountAfterReads readFee ⟨s,pages,old,destination⟩ := by
  unfold mountWords
  dsimp only
  rw [copied,readPage]
  rfl

theorem returning_mount_rows_leaves_exactly_the_paid_writer_output
    (bank : L) (creator : Word key) (group : Word 6)
    (headers : List (OwnerGroup own)) (rootRows : RawRoster own gate key prec page)
    (destination : Meter (List (Word next))) (s : Stamp key prec) (pages : List (Word page)) (old : List D)
    (copied : (gatherOwners rootRows (selectOwnerKeys group headers).result).result=some old)
    (readPage : (readMountedOwners bank creator).result=some (s,pages)) (rows : R)
    (whole : (mountWords bank creator group headers rootRows destination).result=some rows) :
    (writeMountedOwners s pages old destination.result).result=some rows := by
  rw [original_owner_mount_uses_exact_bank_free_write_phase bank creator group headers rootRows
    destination s pages old copied readPage] at whole
  exact whole

#print axioms original_owner_mount_uses_exact_bank_free_write_phase
#print axioms returning_mount_rows_leaves_exactly_the_paid_writer_output
end J6R55SelectedPeak
