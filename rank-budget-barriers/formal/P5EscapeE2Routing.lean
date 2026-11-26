import P5HybridClosureScan
import P5EscapeE2Product

/-! The remaining short execution tests in §9. Calls to a joint predicate
are not free: the accepting bit below is computed from the source's
public edge list and actual Boolean pin reads. -/
namespace Paper5.EscapeE2
open scoped BigOperators Classical
open Paper5.HybridClosure

section Guard
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

noncomputable def coverTest (E : Finset (V×V)) (σ : V→Bool) : Bool×ℕ :=
  scanEdgeList σ E.toList

omit [DecidableEq V] in
theorem cover_test_output (E : Finset (V×V)) (σ : V→Bool) :
    (if (coverTest E σ).1=true then 1 else 0) = PinnedCNF.modelCount (PinnedCNF.formula E σ) := by
  change boolAsNat (coverTest E σ).1 = _
  rw [PinnedCNF.count_eq_indicator]
  have hv := (scanEdgeList_exact σ E.toList).1
  rw [Finset.prod_map_toList] at hv
  exact hv.trans (edge_product_is_indicator E σ)

omit [Fintype V] [DecidableEq V] in
theorem cover_test_cost (E : Finset (V×V)) (σ : V→Bool) :
    (coverTest E σ).2=4*E.card := by
  simpa using (scanEdgeList_exact σ E.toList).2

theorem cloned_cover_test_output (E : Finset (V×V)) (left right : E→Fin 4) (σ : V→Bool) :
    (if (coverTest E σ).1=true then 1 else 0) =
      PinnedCNF.modelCount (MainClonedCNF.formula E left right σ) := by
  rw [MainClonedCNF.modelCount_cloned]
  exact cover_test_output E σ

noncomputable def maskMatrix {E : Finset (V×V)} (M : PinnedCNF.InducedMatching E I) :
    Matrix (I→Bool) (I→Bool) ℚ :=
  Matrix.of fun a b=>(boolAsNat (coverTest E (M.restrictSigns a b)).1:ℚ)

omit [DecidableEq V] in
theorem one_bit_guard_full_rank [DecidableEq I]
    {E : Finset (V×V)} (M : PinnedCNF.InducedMatching E I) :
    (maskMatrix M).rank=2^Fintype.card I ∧
      ∀ σ : V→Bool,(coverTest E σ).2+1=4*E.card+1 := by
  have h : maskMatrix M=M.countMatrix ℚ := by
    ext a b
    change (boolAsNat (coverTest E (M.restrictSigns a b)).1:ℚ)=
      (PinnedCNF.modelCount (PinnedCNF.formula E (M.restrictSigns a b)):ℚ)
    exact_mod_cast cover_test_output E (M.restrictSigns a b)
  refine ⟨by rw [h]; exact M.countMatrix_rank ℚ,fun σ=>?_⟩
  rw [cover_test_cost]

end Guard

def rowTranscript {m : ℕ} (x : Bits m) : List Bool := List.ofFn x

theorem row_transcript_inj {m : ℕ} : Function.Injective (@rowTranscript m) := by
  intro x y h
  apply List.ofFn_injective
  exact h

theorem row_transcript_count (m : ℕ) : Nat.card (Set.range (@rowTranscript m))=2^m := by
  rw [Nat.card_congr (Equiv.ofInjective _ row_transcript_inj).symm,Nat.card_eq_fintype_card]
  simp [Bits]

def matchedPairScan : List (Bool×Bool) → Bool×ℕ
  | [] => (true,0)
  | (a,b)::l =>
    let r := matchedPairScan l
    ((a || b) && r.1,r.2+4)

theorem matched_scan_exact (l : List (Bool×Bool)) :
    (matchedPairScan l).1=(l.map fun xy=>xy.1 || xy.2).all id ∧
    (matchedPairScan l).2=4*l.length := by
  induction l with
  | nil => simp [matchedPairScan]
  | cons ab l ih =>
    obtain ⟨a,b⟩ := ab
    simp [matchedPairScan,ih.1,ih.2,Nat.mul_succ]

/-- Reading and writing the row transcript costs 2m, then there is one
row/column lookup, one OR and one AND at each matched pair. -/
def transcriptRun {m : ℕ} (x y : Bits m) : Bool×ℕ :=
  let row := rowTranscript x
  let q := matchedPairScan (row.zip (List.ofFn y))
  (q.1,q.2+2*row.length)

theorem transcript_run_cost {m : ℕ} (x y : Bits m) :
    (transcriptRun x y).2=6*m := by
  change (matchedPairScan ((rowTranscript x).zip (List.ofFn y))).2+2*(rowTranscript x).length=_
  rw [(matched_scan_exact _).2]
  simp only [rowTranscript,List.length_zip,List.length_ofFn,min_self]
  omega

theorem transcript_run_result {m : ℕ} (x y : Bits m) :
    (transcriptRun x y).1=true ↔ ∀ i,x i=true ∨ y i=true := by
  change (matchedPairScan ((List.ofFn x).zip (List.ofFn y))).1=true ↔ _
  have hz : (List.ofFn x).zip (List.ofFn y)=List.ofFn (fun i=>(x i,y i)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [hz,(matched_scan_exact _).1]
  simp [List.map_ofFn,List.all_eq_true]

/-- Two different worst-case input classes, with a genuinely cheap
one-bit class selector between them. -/
def routeCost (m : ℕ) (route input : Bool) : ℕ :=
  if route=input then 1 else 2^m

def selectedRouteCost (m : ℕ) (input : Bool) : ℕ := 1+routeCost m input input

theorem different_worst_cases (m : ℕ) :
    (∀ route : Bool, ∃ input : Bool,routeCost m route input=2^m) ∧
    (∀ route input : Bool,routeCost m route input≤2^m) ∧
    (∀ input : Bool,selectedRouteCost m input=2) := by
  constructor
  · intro route
    cases route
    · exact ⟨true,by simp [routeCost]⟩
    · exact ⟨false,by simp [routeCost]⟩
  · constructor
    · intro route input
      by_cases h : route=input
      · have h₂ : 0<(2:ℕ)^m := by positivity
        simpa [routeCost,h] using Nat.succ_le_of_lt h₂
      · simp [routeCost,h]
    · intro x
      simp [selectedRouteCost,routeCost]

/-- Applying any canonicalization within a declared local scope stays in
that scope. This makes no global rank claim about canonicalization. -/
theorem scoped_canonicalization {A S R C : Type*} (projection : A→S)
    (fLocal : S→R) (lift : R→C) (x y : A) (h : projection x=projection y) :
    lift (fLocal (projection x))=lift (fLocal (projection y)) := by rw [h]

#print axioms cover_test_output
#print axioms cover_test_cost
#print axioms cloned_cover_test_output
#print axioms one_bit_guard_full_rank
#print axioms row_transcript_inj
#print axioms row_transcript_count
#print axioms matched_scan_exact
#print axioms transcript_run_cost
#print axioms transcript_run_result
#print axioms different_worst_cases
#print axioms scoped_canonicalization
end Paper5.EscapeE2