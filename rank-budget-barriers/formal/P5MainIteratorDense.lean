import P5MainIteratorCoverage
import P5MainIteratorTail

/-! F.A3 uniform bound, with all parameters and actual physical incidences.
The only density condition is the printed real bound on the number of
potentially bad incidences; no assumptions on uniform variable degrees. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {E V F Copy I B : Type*} [Fintype E] [Fintype V]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

theorem finite_FA3 (L : SourceLayout E V F Copy I B) (t : I)
    (R : ℕ) (omitted : Finset ℕ) (hs : omitted.card≤R) (hr : 2≤Fintype.card B)
    (hQ : 256≤Fintype.card I) (hR : 16*R≤Fintype.card I)
    (hcap : ∀ u, cellLoad L u * Fintype.card (WordCell I B)≤2*Fintype.card E)
    (hhalf : 2*(Fintype.card E:ℝ)*(markBase*(3/4:ℝ))^Fintype.card I≤(Fintype.card V:ℝ)/2) :
    ((Fintype.card V:ℝ)/2)*(tailConstant *
      Real.exp (-(64*(R:ℝ)^2/(Fintype.card I:ℝ)))) ≤
      Real.log ((Set.range (sourceTuple (fun j => j∉omitted) L t)).ncard:ℝ) / Real.log 2 := by
  apply actual_FA3_of_escape L t _ _ (mul_nonneg tailConstant_pos.le (Real.exp_nonneg _)) hr hcap hhalf
  intro n hn hq
  exact fair_binomial_uniform_tail _ n R omitted (by omega) hn hq hR hs

#print axioms finite_FA3
end P5MainIterator
