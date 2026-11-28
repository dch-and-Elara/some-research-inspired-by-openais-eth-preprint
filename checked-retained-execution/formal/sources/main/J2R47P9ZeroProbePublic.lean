import FiniteWeightedQueryTree

/-! Address-dependent fixed replies do not affect a weighted adaptive
execution. The public reply may record its center and receiving width. -/
namespace J2R47P9ZeroProbe
open FiniteWeightedQueryTree
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

variable {Q X R S : Type*}

def eliminatePublic (pub : X→S) :
    DecisionTree (Q⊕X) (R⊕S)→DecisionTree Q R
  | .leaf out => .leaf out
  | .ask (.inl q) next => .ask q (fun r=>eliminatePublic pub (next (.inl r)))
  | .ask (.inr x) next => eliminatePublic pub (next (.inr (pub x)))

def withPublic (oracle : Q→R) (pub : X→S) : Q⊕X→R⊕S :=
  Sum.elim (Sum.inl ∘ oracle) (Sum.inr ∘ pub)

theorem eliminatePublic_exact (pub : X→S) (oracle : Q→R) (bill : Q→ℕ)
    (tree : DecisionTree (Q⊕X) (R⊕S)) :
    evaluate (withPublic oracle pub) tree=evaluate oracle (eliminatePublic pub tree) ∧
    paid (Sum.elim bill (fun _=>0)) (withPublic oracle pub) tree=
      paid bill oracle (eliminatePublic pub tree) := by
  induction tree with
  | leaf out => exact ⟨rfl,rfl⟩
  | ask addr next ih =>
    cases addr with
    | inl q =>
      exact ⟨(ih (.inl (oracle q))).1,congrArg (bill q+·) (ih (.inl (oracle q))).2⟩
    | inr x =>
      exact ⟨(ih (.inr (pub x))).1,
        (zero_add _).trans (ih (.inr (pub x))).2⟩

#print axioms eliminatePublic_exact
end J2R47P9ZeroProbe

