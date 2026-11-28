import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

namespace Reconstruction.VisitRuntime

open scoped BigOperators
open MvPolynomial

noncomputable section

/-- A literal using its own separate incidence indeterminate. -/
def signedIncidence {I : Type*} (i : I) (positive : Bool) : MvPolynomial I ℚ :=
  if positive then X i else 1-X i

/-- Clause indicator for two separately indexed incidence indeterminates. -/
def binaryClauseIndicator {E : Type*} (e : E) (a b : Bool) : MvPolynomial (E × Bool) ℚ :=
  1-(1-signedIncidence (e,false) a)*(1-signedIncidence (e,true) b)

def binaryIncidenceProduct {E : Type*} [Fintype E] (signs : E → Bool × Bool) : MvPolynomial (E × Bool) ℚ :=
  ∏ e, binaryClauseIndicator e (signs e).1 (signs e).2

private theorem degree_one_sub {I : Type*} (p : MvPolynomial I ℚ) (hp : 0 < p.totalDegree) :
    (1-p).totalDegree = p.totalDegree := by
  rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt, totalDegree_neg]
  simpa only [totalDegree_one, totalDegree_neg] using hp

private theorem degree_unsatisfied_literal {I : Type*} (i : I) (b : Bool) :
    (1-signedIncidence i b).totalDegree = 1 := by
  cases b
  · simp [signedIncidence, sub_sub_cancel]
  · exact (degree_one_sub (X i) (by simp)).trans (totalDegree_X i)

theorem degree_binaryClauseIndicator {E : Type*} (e : E) (a b : Bool) :
    (binaryClauseIndicator e a b).totalDegree = 2 := by
  have h (i : E × Bool) (s : Bool) : 1-signedIncidence i s ≠ 0 := by
    intro hz
    simpa [hz] using degree_unsatisfied_literal i s
  have hmul : ((1-signedIncidence (e,false) a)*(1-signedIncidence (e,true) b)).totalDegree = 2 := by
    rw [totalDegree_mul_of_isDomain (h (e,false) a) (h (e,true) b), degree_unsatisfied_literal,
      degree_unsatisfied_literal]
  exact (degree_one_sub _ (by rw [hmul]; decide)).trans hmul

/-- Exact pre-substitution degree of the separate-incidence product, for every
choice of literal signs. -/
theorem degree_binaryIncidenceProduct {E : Type*} [Fintype E] (signs : E → Bool × Bool) :
    (binaryIncidenceProduct signs).totalDegree = 2*Fintype.card E := by
  classical
  let f (e : E) := binaryClauseIndicator e (signs e).1 (signs e).2
  have hnonzero (e : E) : f e ≠ 0 := by
    intro hz
    have h := degree_binaryClauseIndicator e (signs e).1 (signs e).2
    change (f e).totalDegree = _ at h
    simp [hz] at h
  have H (S : Finset E) : (∏ e ∈ S, f e).totalDegree = 2*S.card := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert e S he ih =>
      rw [Finset.prod_insert he, Finset.card_insert_of_notMem he,
        totalDegree_mul_of_isDomain (hnonzero e) (Finset.prod_ne_zero_iff.mpr fun j _ => hnonzero j), ih]
      change (binaryClauseIndicator e (signs e).1 (signs e).2).totalDegree + _ = _
      rw [degree_binaryClauseIndicator]
      omega
  simpa only [binaryIncidenceProduct, Finset.card_univ, f] using H Finset.univ

end

end Reconstruction.VisitRuntime
