import P5A11SharpNewton
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Prod.Lex

/-! Determinant of the true Newton-to-Hasse evaluation matrix in
node/jet block order. This is the numerator in the printed confluent
valuation formula, with no unit/distinct-residue premise. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {R T : Type*} [CommRing R] [Fintype T] [LinearOrder T]

abbrev NodeOrder (k : T→ℕ) := Σ u : T, Fin (k u)

def nodeKey {k : T→ℕ} (a : NodeOrder k) : T ×ₗ ℕ :=
  toLex (a.1,a.2.val)

omit [Fintype T] [LinearOrder T] in
theorem nodeKey_injective {k : T→ℕ} : Function.Injective (nodeKey (k:=k)) := by
  rintro ⟨u,i⟩ ⟨v,j⟩ h
  have e : (u,i.val)=(v,j.val) := congrArg ofLex h
  have hu : u=v := congrArg Prod.fst e
  subst v
  have hi : i=j := Fin.ext (congrArg Prod.snd e)
  subst j
  rfl

noncomputable def newtonEvaluation (t a : T→R) (k : T→ℕ) :
    Matrix (NodeOrder k) (NodeOrder k) R :=
  fun row col => (affinePolynomial (t row.1) (a row.1)
    (newtonColumn t k col.1 col.2.val)).coeff row.2.val

theorem newton_matrix_early_zero (t a : T→R) (k : T→ℕ) (i j : NodeOrder k)
    (h : nodeKey i < nodeKey j) :
    newtonEvaluation t a k i j=0 := by
  rcases i with ⟨u,s⟩
  rcases j with ⟨v,r⟩
  change Prod.Lex (· < ·) (· < ·) (u,s.val) (v,r.val) at h
  rw [Prod.lex_def] at h
  rcases h with huv|⟨rfl,hs⟩
  · exact newton_earlier_node_zero t a k u v s.val r.val huv s.isLt
  · exact newton_smaller_order_zero t a k u s.val r.val hs

theorem det_newtonEvaluation (t a : T→R) (k : T→ℕ) :
    (newtonEvaluation t a k).det =
      ∏ u : T,∏ j : Fin (k u),((a u)^j.val*(∏ s∈earlierNodes u,(t u-t s)^(k s))) := by
  letI : LinearOrder (NodeOrder k) := LinearOrder.lift' nodeKey nodeKey_injective
  rw [Matrix.det_of_lowerTriangular (newtonEvaluation t a k) (by
    intro i j h
    exact newton_matrix_early_zero t a k i j h)]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro j _
  exact newton_diagonal_entry t a k u j.val

#print axioms newton_matrix_early_zero
#print axioms det_newtonEvaluation
end Paper5
