import J4R43LiteralOutsideConditionalScore
import J4R43LiteralOutsideBalance

/-! The graph-only derandomizer fixes the actual fair marks one at a
time. Its comparison uses the local moment expression, never the
exponential semantic sum used to prove that expression correct. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open IndependentThinning J6R10Repack P11FullPacking
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4800000

variable {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

def chooseMark (B : U→Finset U) (label : U→C) (a : U→Option Bool) (i : U) : U→Option Bool :=
  if a i=none then
    let a0 := Function.update a i (some false)
    let a1 := Function.update a i (some true)
    if localScore a0 B label ≤ localScore a1 B label then a0 else a1
  else a

theorem choose_maintains (B : U→Finset U) (label : U→C)
    (a : U→Option Bool) (i e : U) (h : a e≠none) :
    chooseMark B label a i e=a e := by
  unfold chooseMark
  by_cases fit : a i=none
  · have neq : e≠i := fun eq=>h (eq ▸ fit)
    rw [if_pos fit]
    split_ifs <;> simp [Function.update_of_ne neq]
  · rw [if_neg fit]

theorem choose_fills (B : U→Finset U) (label : U→C) (a : U→Option Bool) (i : U) :
    chooseMark B label a i i≠none := by
  unfold chooseMark
  by_cases fresh : a i=none
  · rw [if_pos fresh]
    split_ifs <;> simp
  · simp [fresh]

theorem choose_does_not_raise (B : U→Finset U) (label : U→C)
    (a : U→Option Bool) (i : U) :
    localScore (chooseMark B label a i) B label≤localScore a B label := by
  unfold chooseMark
  by_cases new : a i=none
  · rw [if_pos new]
    have h := conditional_split a i new (rawScore B label)
    simp only [←local_score_exact] at h
    dsimp only
    split_ifs with yes
    · linarith
    · have lt := lt_of_not_ge yes
      linarith
  · rw [if_neg new]

def fillMarks (B : U→Finset U) (label : U→C) : List U→(U→Option Bool)→(U→Option Bool)
  | [],a=>a
  | i::rest,a=>fillMarks B label rest (chooseMark B label a i)

theorem fill_maintains (B : U→Finset U) (label : U→C) (lst : List U)
    (a : U→Option Bool) (e : U) (hs : a e≠none) :
    fillMarks B label lst a e=a e := by
  induction lst generalizing a with
  | nil => rfl
  | cons i rest ih =>
    rw [fillMarks]
    have h := choose_maintains B label a i e hs
    rw [ih _ (by rw [h]; exact hs),h]

theorem fill_all_requested (B : U→Finset U) (label : U→C) (lst : List U)
    (a : U→Option Bool) (e : U) (hs : e∈lst) :
    fillMarks B label lst a e≠none := by
  induction lst generalizing a with
  | nil => simp at hs
  | cons i rest ih =>
    rw [fillMarks]
    rcases List.mem_cons.mp hs with rfl|old
    · have h := choose_fills B label a e
      rw [fill_maintains B label rest _ _ h]
      exact h
    · exact ih _ old

theorem fill_does_not_raise (B : U→Finset U) (label : U→C) (lst : List U)
    (a : U→Option Bool) :
    localScore (fillMarks B label lst a) B label≤localScore a B label := by
  induction lst generalizing a with
  | nil => exact le_rfl
  | cons i rest ih =>
    exact (ih (chooseMark B label a i)).trans (choose_does_not_raise B label a i)

def deterministicMarks (B : U→Finset U) (label : U→C) : U→Bool :=
  fun e=>(fillMarks B label (Finset.univ : Finset U).toList (fun _=>none) e).getD false

theorem deterministic_marks_score (B : U→Finset U) (label : U→C) :
    rawScore B label (deterministicMarks B label)≤localScore (fun _=>none) B label := by
  let ns := (Finset.univ : Finset U).toList
  let S := fillMarks B label ns (fun _=>none)
  have full : S=fun e=>some (deterministicMarks B label e) := by
    funext e
    have live : S e≠none := fill_all_requested B label ns (fun _=>none) e (by simp [ns])
    unfold deterministicMarks
    change S e=some ((S e).getD false)
    cases h : S e
    · exact (live h).elim
    · rfl
  have all := fill_does_not_raise B label ns (fun _=>none)
  change localScore S B label≤_ at all
  rw [full,local_score_exact,conditional_full_exact] at all
  exact all

theorem deterministic_variance_bound (B : U→Finset U) (label : U→C) (D : ℕ)
    (self : ∀ e,e∈B e) (symm : ∀ e f,f∈B e→e∈B f) (short : ∀ e,(B e).card≤D) :
    rawScore B label (deterministicMarks B label)≤4*(Fintype.card U:ℚ)*(D*D:ℕ) :=
  (deterministic_marks_score B label).trans (literal_initial_score_bound B label D self symm short)

/-- Each comparison has two candidate objectives; each cell uses once
each real ordered pair plus once each edge. The block-scanning factor
is separate (at most 2D positions, with D for consistency). -/
theorem greedy_exact_visit_count :
    Nat.card (U×Bool×((C×U×U)⊕(C×U)))=
      2*Fintype.card U*Fintype.card C*(Fintype.card U^2+Fintype.card U) := by
  simp [Nat.card_prod,Nat.card_sum,Nat.card_eq_fintype_card]
  ring

#print axioms choose_maintains
#print axioms choose_fills
#print axioms choose_does_not_raise
#print axioms fill_maintains
#print axioms fill_all_requested
#print axioms fill_does_not_raise
#print axioms deterministic_marks_score
#print axioms deterministic_variance_bound
#print axioms greedy_exact_visit_count
end
end J4R43LiteralOutside

