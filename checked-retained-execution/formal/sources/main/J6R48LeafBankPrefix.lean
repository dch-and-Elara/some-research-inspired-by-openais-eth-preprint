import J6R33StatefulArithmeticPageLeaf
import J6R30ProducedGateRegistryPrefix
import J6R30ProducedGateRegistryDFS

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000
set_option maxRecDepth 2200

/-! Price the actual extra historical prefix in the append-only
resident implementation. A successful old read remains the same value
but is charged bit comparisons for *every* intervening header. This
must not be conflated with an ancestry-only stack or a free pointer. -/
namespace J6R48Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10
open J6R21Ancestor J6R22Active J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "Bnk" => PageBank f ell key prec tw bw page
local notation "Rec" => Stored key prec tw bw (PagedEnvelope f ell prec page)

def bump {T : Type*} (u : Meter T) (n : ℕ) : Meter T := ⟨u.result,u.steps+n⟩

theorem consume_page_grown {p : ℕ} (hf : f.Monic) (F : Frame f p) (hEll : 0<ell)
    (addr : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page)
    (dep : ℕ) (wires : List WireRead) (bits : List Bool)
    (before after : Bnk) (front : List (RefRow key Rec))
    (grown : after.records=front++before.records) (away : ∀ r∈front,r.address≠addr) :
    consumePage hf F hEll addr pg dep wires bits after=
      bump (consumePage hf F hEll addr pg dep wires bits before) (front.length*refHeadFee key) := by
  have pay := reference_front_fee addr front before.records away
  unfold consumePage
  dsimp only
  rw [grown,pay]
  generalize eq : locate addr before.records=first
  obtain ⟨r,outer⟩ := first
  cases r with
  | none => simp [bump,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  | some r =>
    generalize rel : locate pg r.payload.pages=second
    obtain ⟨data,inner⟩ := second
    cases data <;> simp [rel,bump,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem read_page_grown {p : ℕ} (hf : f.Monic) (F : Frame f p) (hEll : 0<ell)
    (addr : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page)
    (dep : ℕ) (wires : List WireRead) (bits : List Bool)
    (before after : Bnk) (front : List (RefRow key Rec))
    (grown : after.records=front++before.records) (away : ∀ r∈front,r.address≠addr) :
    readPage hf F hEll addr pg dep wires bits after=
      bump (readPage hf F hEll addr pg dep wires bits before) (front.length*refHeadFee key) := by
  unfold readPage
  rw [consume_page_grown hf F hEll addr pg dep wires bits before after front grown away]
  unfold requireWord bump
  dsimp only
  cases e : (consumePage hf F hEll addr pg dep wires bits before).result <;> dsimp only
  all_goals congr 1; omega

theorem read_page_after_actual_jobs {p : ℕ} (hf : f.Monic) (F : Frame f p) (hEll : 0<ell)
    (addr : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page)
    (dep : ℕ) (wires : List WireRead) (bits : List Bool)
    (before : Bnk) (jobs : List (PageJob f ell key prec tw bw page))
    (away : ∀ r∈(jobs.map Job.immutable).reverse,r.address≠addr) :
    readPage hf F hEll addr pg dep wires bits (afterJobs before jobs)=
      bump (readPage hf F hEll addr pg dep wires bits before) (jobs.length*refHeadFee key) := by
  have h := read_page_grown hf F hEll addr pg dep wires bits before (afterJobs before jobs)
    (jobs.map Job.immutable).reverse (after_jobs_views before jobs).2 away
  simpa only [List.length_reverse,List.length_map] using h

#print axioms consume_page_grown
#print axioms read_page_grown
#print axioms read_page_after_actual_jobs
end J6R48Leaf
