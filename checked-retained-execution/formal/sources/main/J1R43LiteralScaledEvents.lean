import J1R43LiteralBudget
import J1R43LiteralDenominator

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4300000
set_option linter.unusedSectionVars false

/-! Use the one denominator r^(4Q) for the actual conditional
J1 events. This prevents artificial repeated products of the different
local rational denominators. -/
namespace J1R43Literal
open scoped BigOperators
open DiagonalAbundance J1MainSourceLabels
noncomputable section

section Support
variable {P S : Type*} [DecidableEq P] [Fintype S] [DecidableEq S] [Nonempty S]

theorem support_bound_of_reads {T I : Type*} [Fintype T] [Fintype I]
    (key : T × I → P) (test : (T × I → S) → Bool) (ht : Fintype.card T≤4) :
    (LocalTest.fromReads key test).support.card≤4*Fintype.card I := by
  unfold LocalTest.fromReads
  exact Finset.card_image_le.trans (by
    rw [Finset.card_univ,Fintype.card_prod]
    exact Nat.mul_le_mul_right _ ht)

def scaledEventNumerator (Q : ℕ) (x : LocalTest P S) (a : P → Option S) : ℕ :=
  Fintype.card S^(4*Q-x.support.card)*integerProbability x a

theorem scaled_event_exact (Q : ℕ) (x : LocalTest P S) (a : P → Option S)
    (hlen : x.support.card≤4*Q) :
    (scaledEventNumerator Q x a:ℚ) =
      (Fintype.card S:ℚ)^(4*Q)*x.conditional (partialWeight a) := by
  unfold scaledEventNumerator
  push_cast
  rw [integerProbability_exact,← mul_assoc,← pow_add,Nat.sub_add_cancel hlen]

theorem scaled_event_height (Q : ℕ) (x : LocalTest P S) (a : P → Option S)
    (hlen : x.support.card≤4*Q) :
    scaledEventNumerator Q x a ≤ Fintype.card S^(4*Q) := by
  unfold scaledEventNumerator
  calc
    _ ≤ Fintype.card S^(4*Q-x.support.card) * Fintype.card S^x.support.card :=
      Nat.mul_le_mul_left _ (local_integer_height x a).1
    _ = _ := by rw [← pow_add,Nat.sub_add_cancel hlen]

end Support

section Visit
variable {V F B I S E A : Type*} [DecidableEq V] [DecidableEq F] [DecidableEq B]
    [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S] [Nonempty S]
local notation "P" => Primitive V F B I

theorem actual_visit_support (t : I) (tag : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (j : ScoreVisit E V A I S) :
    (scoreVisit t tag var fac pin j).support.card≤4*Fintype.card I := by
  rcases j with z|z
  · change (incidenceEvent t tag var fac z.1 z.2).support.card≤_
    apply support_bound_of_reads
    simp [Roles]
  rcases z with z|z
  · change (variableEvent (F:=F) (B:=B) (S:=S) z.2.1 z.2.2 z.1).support.card≤_
    apply support_bound_of_reads
    simp
  rcases z with ⟨j,z⟩
  rcases z with b|a
  · change (hitPairEvent t tag var fac j.1 j.2 (pin b.1) (pin b.2)).support.card≤_
    apply support_bound_of_reads
    simp [Roles]
  · change (hitPairEvent t tag var fac j.1 j.2 (pin a) (pin a)).support.card≤_
    apply support_bound_of_reads
    simp [Roles]

theorem actual_visit_scaled (t : I) (tag : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (j : ScoreVisit E V A I S) (a : P → Option S) :
    let x := scoreVisit t tag var fac pin j
    (scaledEventNumerator (Fintype.card I) x a:ℚ) =
      (Fintype.card S:ℚ)^(4*Fintype.card I)*x.conditional (partialWeight a) ∧
    scaledEventNumerator (Fintype.card I) x a ≤ Fintype.card S^(4*Fintype.card I) := by
  have h := actual_visit_support t tag var fac pin j
  exact ⟨scaled_event_exact _ _ _ h,scaled_event_height _ _ _ h⟩

end Visit

#print axioms support_bound_of_reads
#print axioms scaled_event_exact
#print axioms scaled_event_height
#print axioms actual_visit_support
#print axioms actual_visit_scaled

end
end J1R43Literal