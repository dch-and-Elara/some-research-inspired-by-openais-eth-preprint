import J1R43LiteralBudget

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7100000
set_option linter.unusedSectionVars false

/-! The exact objective is one signed weighted roster scan over the
visits charged by the polynomial count. The baseline terms use the
known cardinalities and do not traverse any assignment space. -/
namespace J1R43Literal
open scoped BigOperators
open DiagonalAbundance J1MainSourceLabels
noncomputable section

variable {V F B I S E A : Type*}
  [Fintype V] [Fintype F] [Fintype B] [Fintype I] [Fintype S] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq F] [DecidableEq B] [DecidableEq I] [DecidableEq S] [Nonempty S]

theorem score_roster_exact (t : I) (tag : F → Option B) (var : E → V) (fac : E → F)
    (pin : A → E) (mu : ℚ) (w : Marginals (Primitive V F B I) S) :
    localScore t tag var fac pin mu w =
      constantTerm (E:=E) (V:=V) (I:=I) (S:=S) mu +
        ∑ j : ScoreVisit E V A I S,
          coefficient mu j * (scoreVisit t tag var fac pin j).conditional w := by
  unfold localScore phiLocal xiLocal varianceLocal constantTerm
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,coefficient,scoreVisit,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  ring

#print axioms score_roster_exact

end
end J1R43Literal