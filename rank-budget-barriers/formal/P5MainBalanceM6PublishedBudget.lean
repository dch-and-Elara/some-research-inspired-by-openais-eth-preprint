import P5MainBalanceM6PublishedChart
import P5MainBalanceM6ExactBudget

/-! A cardinal-normalization wrapper. Transport only the exact numeric
(2D+1) bound into the actual measurement box, not a source identity. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Real
open scoped BigOperators Classical

variable {E W F Copy I B : Type*}
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

set_option maxHeartbeats 4000000 in
theorem exactBox_hyp_from_numeric (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (N ell Q r : ℕ) (ε : ℝ)
    (hQ : Fintype.card I=Q) (hr : Fintype.card B=r)
    (h : ∀ j : ℕ,
      (j:ℝ)*log (2*(Q:ℝ))≤ε*(N:ℝ)/sqrt (Q:ℝ) →
      ((((2*Fintype.card (WordCell I B)+1)^(r*(Fintype.card Copy*
        Fintype.card (Exceptional (Unequal (I:=I) (B:=B)) keep))))*ell*(j+1):ℕ):ℝ)≤
        exp (ε*(N:ℝ)/sqrt (Q:ℝ))) :
    ∀ j : ℕ,
      (j:ℝ)*log (2*(Fintype.card I:ℝ))≤ε*(N:ℝ)/sqrt (Fintype.card I:ℝ) →
      ((exactBox keep L*ell*(j+1):ℕ):ℝ)≤exp (ε*(N:ℝ)/sqrt (Fintype.card I:ℝ)) := by
  rw [exactBox_eq_copied_rows keep L, hQ, hr]
  exact h

#print axioms exactBox_hyp_from_numeric
end P5MainBalance.M6
