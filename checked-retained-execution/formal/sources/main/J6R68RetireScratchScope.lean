import J6R68RetireScratchCore
import J6R68RecursivePeakScope

/-! One local observation at retirement. The conservative overlap
still counts the fully mounted child and only one copy of the selected
inherited payload. The original result restores the exact saved
logical tails. No garbage-collection or byte-level pointer claim. -/
namespace J6R68.RetireScratch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R57ScopeFee J6R64Active J6R66.BootPeak J6R68.RecursivePeak

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 3900

variable {f : ℤ[X]} {ell key prec tw bw page width : ℕ} {Out : Type}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def selectedRetireOverlap (held : ℕ) (live : L) (obs : TailCopyObservation width) : ℕ :=
  held+mountedSelectedBits live+obs.selectedBits

theorem observed_paid_scope_retires_the_actual_child_to_its_parent
    (tails : SavedDirectoryTails width) (j : J)
    (go : (R : L) → OwnsHeader j.entry.result R → Meter (Out×L))
    (bad : Meter Out) (B : L) (ready : JobsReady B [j]) (held : ℕ) :
    let live := afterOne B j
    let seen := observeHeaderScope tails j go bad B
    seen.2=some ⟨tails,tails⟩ ∧
      seen.1.result.2=B ∧ seen.1.result.2.headers=live.headers.tail ∧
      seen.1.result.2.records=live.records.tail ∧
      selectedRetireOverlap held live (⟨tails,tails⟩ : TailCopyObservation width)=
        held+mountedSelectedBits B+mountedInsertionBits j+4*width := by
  dsimp only
  have copies := legal_header_observes_exact_tail_copy tails j go bad B ready
  have value := congrArg Meter.result
    (the_actual_header_scope_enters_its_published_head (retireSavedDirectory tails) j go bad B ready)
  rw [observed_header_projects_to_same_actual_meter,value]
  refine ⟨copies,rfl,rfl,rfl,?_⟩
  unfold selectedRetireOverlap
  rw [publication_adds_exact_selected_record,observed_source_and_copy_are_four_words]
  ac_rfl

theorem retained_child_plus_one_return_pair_is_bounded
    (tails : SavedDirectoryTails width) (j : J) (B : L)
    (held H : ℕ) (childRoof : held+mountedSelectedBits (afterOne B j) ≤ H) :
    selectedRetireOverlap held (afterOne B j) (⟨tails,tails⟩ : TailCopyObservation width) ≤ H+4*width ∧
      held+mountedSelectedBits B ≤ H := by
  constructor
  · unfold selectedRetireOverlap
    rw [observed_source_and_copy_are_four_words]
    exact Nat.add_le_add_right childRoof _
  · rw [publication_adds_exact_selected_record] at childRoof
    exact (Nat.add_le_add_left (Nat.le_add_right _ _) _).trans childRoof

#print axioms observed_paid_scope_retires_the_actual_child_to_its_parent
#print axioms retained_child_plus_one_return_pair_is_bounded
end J6R68.RetireScratch
