import J1R43LiteralEvents

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000
set_option linter.unusedSectionVars false

/-! Exact conditional evaluation of all three terms of the printed J1
score. The pair expansions are ordered and include the diagonal.
Different abundance counters need not be mutually independent. -/
namespace J1R43Literal
open scoped BigOperators
open DiagonalAbundance J1MainSourceLabels J1MainSourceCollision
open GuardExpectation (average average_sum average_const average_add average_mulConst)
noncomputable section

section Linearity
variable {P S : Type*} [Fintype P] [DecidableEq P] [Fintype S]

theorem avg_sub (w : P → S → ℚ) (f g : (P → S) → ℚ) :
    average w (fun z => f z - g z) = average w f - average w g := by
  simp only [average,mul_sub,Finset.sum_sub_distrib]

theorem avg_div (w : P → S → ℚ) (f : (P → S) → ℚ) (q : ℚ) :
    average w (fun z => f z / q) = average w f / q := by
  simp only [div_eq_mul_inv, mul_comm _ q⁻¹]
  exact average_mulConst w f q⁻¹

end Linearity

section Source
variable {V F B I S E A : Type*}
  [Fintype V] [Fintype F] [Fintype B] [Fintype I] [Fintype S] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq F] [DecidableEq B] [DecidableEq I] [DecidableEq S]
  [Nonempty S]

local notation "P" => Primitive V F B I

def phiLocal (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (w : P → S → ℚ) : ℚ :=
  ∑ p : E × E, ((incidenceEvent special tie var fac p.1 p.2).conditional w -
    1/(Fintype.card (Draw I S):ℚ))

theorem phiLocal_exact (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (w : P → S → ℚ) (hw : ∀ i, ∑ a, w i a = 1) :
    average w (incidenceCost special tie var fac) = phiLocal special tie var fac w := by
  unfold incidenceCost phiLocal
  simp_rw [deviation_eq_pairs, average_sum, avg_sub, average_const w hw,
    ← incidenceEvent_value, local_conditional _ w hw]

def xiLocal (w : P → S → ℚ) : ℚ :=
  ∑ t : I, ∑ p : V × V, ((variableEvent p.1 p.2 t).conditional w - 1/(Fintype.card S:ℚ))

theorem xiLocal_exact (w : P → S → ℚ) (hw : ∀ i, ∑ a, w i a = 1) :
    average w variableCost = xiLocal w := by
  unfold variableCost xiLocal
  simp_rw [deviation_eq_pairs, average_sum, avg_sub, average_const w hw,
    ← variableEvent_value, local_conditional _ w hw]

def actualCount (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (j : I × S) (z : P → S) : ℚ :=
  hitCount j.1 j.2 ((literalCell special tie var fac z) ∘ pin)

def varianceLocal (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (j : I × S) (mu : ℚ) (w : P → S → ℚ) : ℚ :=
  let h := fun a b : A =>
    (hitPairEvent special tie var fac j.1 j.2 (pin a) (pin b)).conditional w
  (∑ p : A × A, h p.1 p.2) - 2*mu*(∑ a : A, h a a) + mu^2

theorem varianceLocal_exact (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (j : I × S) (mu : ℚ) (w : P → S → ℚ)
    (hw : ∀ i, ∑ a, w i a = 1) :
    average w (fun z => (actualCount special tie var fac pin j z - mu)^2) =
      varianceLocal special tie var fac pin j mu w := by
  let h := fun a : A => fun z : P → S => hit j.1 j.2 (literalCell special tie var fac z (pin a))
  have he (z : P → S) :
      (actualCount special tie var fac pin j z - mu)^2 =
        (∑ p : A × A, h p.1 z * h p.2 z) - 2*mu*(∑ a : A, h a z) + mu^2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    change ((∑ a, h a z)-mu)^2 =
      (∑ a, h a z)*(∑ a, h a z)-2*mu*(∑ a, h a z)+mu^2
    ring
  simp_rw [he,average_add,avg_sub,average_sum,average_mulConst,average_const w hw]
  unfold h varianceLocal
  simp_rw [← hitPairEvent_value, ← singleHitEvent_value, average_sum, local_conditional _ w hw]

def printedScore (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (mu : ℚ) (z : P → S) : ℚ :=
  jointScore (fun c => incidenceCost special tie var fac c / (5*(Fintype.card E:ℚ)) +
      variableCost c / ((Fintype.card I:ℚ)*Fintype.card V))
    (actualCount special tie var fac pin) mu z

def localScore (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (mu : ℚ) (w : P → S → ℚ) : ℚ :=
  phiLocal special tie var fac w / (5*(Fintype.card E:ℚ)) +
    xiLocal w / ((Fintype.card I:ℚ)*Fintype.card V) +
    8*(∑ j : I × S, varianceLocal special tie var fac pin j mu w) / mu^2

theorem exact_conditional_printed_score (special : I) (tie : F → Option B)
    (var : E → V) (fac : E → F) (pin : A → E) (mu : ℚ)
    (w : P → S → ℚ) (hw : ∀ i, ∑ a, w i a = 1) :
    average w (printedScore special tie var fac pin mu) =
      localScore special tie var fac pin mu w := by
  unfold printedScore jointScore localScore
  rw [average_add,average_add,avg_div,avg_div,avg_div,average_mulConst,average_sum,
    phiLocal_exact special tie var fac w hw,xiLocal_exact w hw]
  simp_rw [varianceLocal_exact special tie var fac pin _ mu w hw]

end Source

#print axioms avg_sub
#print axioms avg_div
#print axioms phiLocal_exact
#print axioms xiLocal_exact
#print axioms varianceLocal_exact
#print axioms exact_conditional_printed_score

end
end J1R43Literal