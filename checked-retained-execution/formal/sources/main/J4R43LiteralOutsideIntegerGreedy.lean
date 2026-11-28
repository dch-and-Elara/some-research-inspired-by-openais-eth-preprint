import J4R43LiteralOutsideScoreInteger
import J4R43LiteralOutsideDeterministicSupply

/-! Replace each original conditional-score comparison by the exact
integer comparison, preserving even the tie-break and every written
edge mark. Same selected matching, no rational evaluator required. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open IndependentThinning P11FullPacking J6R10Repack
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4200000

variable {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

def chooseIntegerMark (B : U→Finset U) (label : U→C) (D : ℕ) (a : U→Option Bool) (i : U) : U→Option Bool :=
  if a i=none then
    let a0 := Function.update a i (some false)
    let a1 := Function.update a i (some true)
    if scoreInteger a0 B label D≤scoreInteger a1 B label D then a0 else a1
  else a

theorem chooses_the_same_real_bit (B : U→Finset U) (label : U→C) (D : ℕ)
    (scope : ∀ e,(B e).card≤D) (a : U→Option Bool) (i : U) :
    chooseIntegerMark B label D a i=chooseMark B label a i := by
  unfold chooseIntegerMark chooseMark
  by_cases h : a i=none
  · simp only [if_pos h]
    simp only [same_greedy_integer_comparison _ _ B label D scope]
  · rw [if_neg h,if_neg h]

def fillIntegerMarks (B : U→Finset U) (label : U→C) (D : ℕ) :
    List U→(U→Option Bool)→(U→Option Bool)
  | [],a=>a
  | i::rest,a=>fillIntegerMarks B label D rest (chooseIntegerMark B label D a i)

theorem fills_same_marks (B : U→Finset U) (label : U→C) (D : ℕ)
    (scope : ∀ e,(B e).card≤D) (order : List U) (a : U→Option Bool) :
    fillIntegerMarks B label D order a=fillMarks B label order a := by
  induction order generalizing a with
  | nil => rfl
  | cons i rest ih =>
    rw [fillIntegerMarks,fillMarks,chooses_the_same_real_bit B label D scope,ih]

def deterministicIntegerMarks (B : U→Finset U) (label : U→C) (D : ℕ) : U→Bool :=
  fun e=>(fillIntegerMarks B label D (Finset.univ : Finset U).toList (fun _=>none) e).getD false

theorem exact_same_physical_marks {E A B G : Type} [Fintype E] [Fintype G] [LinearOrder G] {a : ℕ}
    {N : Network E A B} (P : PhysicalPacking N a G) (pin : E)
    (dr : ∀ u : A,Nat.card {e : E//N.row e=u}≤3) (dc : ∀ u : B,Nat.card {e : E//N.col e=u}≤3) :
    deterministicIntegerMarks (block N pin) (realColour P pin) 5 =
      deterministic_source_marks P pin := by
  unfold deterministicIntegerMarks deterministic_source_marks deterministicMarks
  rw [fills_same_marks (block N pin) (realColour P pin) 5 (literal_block_count N 3 dr dc pin)]

#print axioms chooses_the_same_real_bit
#print axioms fills_same_marks
#print axioms exact_same_physical_marks
end
end J4R43LiteralOutside

