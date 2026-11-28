
import J6R49NonModeStackPayload
import J6R22ActiveGroups

/-! Exact suspension of the actual paid right fold used for completed
centre contributions, under head-before-tail evaluation.  The flat
payload only describes the retained numerical blocks. -/
namespace J6R50Peak
open A1R10 A1R12 AOracleMachineTime J6R21Leaf J6R22Active J6R49NonModeStack

set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {p ell : ℕ} {fw : List (Word p)}

def resumeBlocks (hp : 0<p) (saved : List (Meter (UVBlock fw ell)))
    (later : Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  saved.foldr (addM hp) later

theorem paid_sum_suspends {A : Type*} (hp : 0<p) (read : A→Meter (UVBlock fw ell))
    (before after : List A) :
    sumM hp read (before++after)=resumeBlocks hp (before.map read) (sumM hp read after) := by
  induction before with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append,sumM,List.map_cons,resumeBlocks,List.foldr_cons] at ih ⊢
    rw [ih]

theorem paid_sum_resumes_at {A : Type*} (hp : 0<p) (read : A→Meter (UVBlock fw ell))
    (before : List A) (a : A) (after : List A) (value : Meter (UVBlock fw ell))
    (eq : read a=value) :
    sumM hp read (before++a::after)=
      resumeBlocks hp (before.map read) (addM hp value (sumM hp read after)) := by
  rw [paid_sum_suspends]
  simp only [sumM,eq]

def completedBlockPayload (saved : List (Meter (UVBlock fw ell))) : List Bool :=
  coeffPayload (saved.map (fun w=>w.result))

theorem completed_block_payload_exact (saved : List (Meter (UVBlock fw ell))) :
    (completedBlockPayload saved).length=saved.length*(ell*(fw.length*p)) := by
  rw [completedBlockPayload,coeff_payload_length,List.length_map]

#print axioms paid_sum_suspends
#print axioms paid_sum_resumes_at
#print axioms completed_block_payload_exact
end J6R50Peak
