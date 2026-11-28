import V8CapacitySpecialChoices
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Arbitrary residue field, L=0 and p=1: normalize monomial exponents,
sum all collisions in the actual field, then get exact rank from the
bounded coefficient matrix. Evaluation is tensor Vandermonde. -/
namespace V8CapacitySpecialResidue
open scoped Classical BigOperators

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {K E J : Type*} [Field K] [Fintype K] [Fintype E]

local notation "q" => Fintype.card K
local notation "Words" => (E → Fin q)

def reducedExponent (n : ℕ) : ℕ :=
  if n=0 then 0 else ((n-1)%(q-1))+1

theorem redExp_lt (n : ℕ) : reducedExponent (K:=K) n<q := by
  unfold reducedExponent
  have hq : 1<q := Fintype.one_lt_card
  split_ifs
  · omega
  · have hm := Nat.mod_lt (n-1) (show 0<q-1 by omega)
    omega

theorem reduced_power (x : K) (n : ℕ) :
    x^reducedExponent (K:=K) n=x^n := by
  by_cases hn : n=0
  · simp [hn,reducedExponent]
  · rw [reducedExponent,if_neg hn]
    by_cases hx : x=0
    · subst x
      rw [zero_pow (by omega),zero_pow hn]
    · have he : n=((n-1)%(q-1)+1)+(q-1)*((n-1)/(q-1)) := by
        have h := Nat.mod_add_div (n-1) (q-1)
        omega
      -- Only replace the right-hand exponent; the normal exponent is
      -- computed from the original n.
      conv_rhs => rw [he,pow_add,pow_mul,FiniteField.pow_card_sub_one_eq_one x hx,one_pow,mul_one]

def normalWord (m : E →₀ ℕ) : Words :=
  fun e => ⟨reducedExponent (K:=K) (m e),redExp_lt (K:=K) _⟩

/-- This is a sum of original coefficients, rather than a count of
distinct ordinary terms. Terms can cancel in the actual residue field. -/
def normalCoeff (f : MvPolynomial E K) (r : Words) : K :=
  ∑ m ∈ f.support, if r=normalWord m then f.coeff m else 0

def tensorMatrix (V : Matrix (Fin q) (Fin q) K) : Matrix Words Words K :=
  Matrix.of fun a b => ∏ e : E, V (a e) (b e)

theorem tensor_composition (L R : Matrix (Fin q) (Fin q) K) :
    tensorMatrix (E:=E) L*tensorMatrix R=tensorMatrix (L*R) := by
  ext a b
  simp only [Matrix.mul_apply,tensorMatrix,Matrix.of_apply,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun e (j : Fin q) => L (a e) j*R j (b e))).symm

theorem tensor_identity : tensorMatrix (E:=E) (1 : Matrix (Fin q) (Fin q) K)=1 := by
  ext a b
  by_cases h : a=b
  · subst b
    simp [tensorMatrix]
  · have hn : ∃ e, a e≠b e := by
      by_contra! hz
      exact h (funext hz)
    obtain ⟨e,he⟩ := hn
    rw [Matrix.one_apply,if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

def fieldEvaluation (e : Fin q ≃ K) : Matrix Words Words K :=
  tensorMatrix (Matrix.vandermonde e)

def fieldReceiver (e : Fin q ≃ K) : Matrix Words Words K :=
  tensorMatrix (Matrix.vandermonde e)⁻¹

theorem receives_exactly (e : Fin q ≃ K) :
    (fieldReceiver (E:=E) e)*(fieldEvaluation e)=1 := by
  unfold fieldReceiver fieldEvaluation
  have h : IsUnit (Matrix.vandermonde e).det :=
    (Matrix.det_vandermonde_ne_zero_iff.mpr e.injective).isUnit
  rw [tensor_composition,Matrix.nonsing_inv_mul _ h,tensor_identity]

theorem evaluate_after_reduction (e : Fin q ≃ K) (f : MvPolynomial E K) (x : Words) :
    (fieldEvaluation e).mulVec (normalCoeff f) x=MvPolynomial.eval (fun j => e (x j)) f := by
  have hd := congrArg (MvPolynomial.eval (fun j => e (x j))) (MvPolynomial.as_sum f)
  simp only [map_sum,MvPolynomial.eval_monomial,Finsupp.prod_pow] at hd
  rw [hd]
  simp only [Matrix.mulVec,dotProduct,fieldEvaluation,tensorMatrix,Matrix.of_apply,
    Matrix.vandermonde_apply,normalCoeff,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_eq_single_of_mem (normalWord m) (Finset.mem_univ _)]
  · simp only [if_true]
    unfold normalWord
    simp only [reduced_power,mul_comm]
  · intro r _ hr
    rw [if_neg hr]

variable [Fintype J]

def reducedCoefficientMatrix (f : J → MvPolynomial E K) :
    Matrix Words J K := Matrix.of fun r j => normalCoeff (f j) r

def residueEvaluationMatrix (e : Fin q ≃ K) (f : J → MvPolynomial E K) :
    Matrix Words J K := Matrix.of fun a j => MvPolynomial.eval (fun e' => e (a e')) (f j)

theorem evaluates_matrix (e : Fin q ≃ K) (f : J → MvPolynomial E K) :
    residueEvaluationMatrix e f = fieldEvaluation e*reducedCoefficientMatrix f := by
  ext i j
  exact (evaluate_after_reduction e (f j) i).symm

section GenericRank
variable {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A]

theorem rank_after_invertible_left (L V : Matrix A A K) (P : Matrix A C K) (h : L*V=1) :
    (V*P).rank=P.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right V P)
  calc
    P.rank=(L*(V*P)).rank := by rw [← Matrix.mul_assoc,h,Matrix.one_mul]
    _≤(V*P).rank := Matrix.rank_mul_le_right L (V*P)

end GenericRank


/-- Exactly the rank of the whole field grid, with no large-residue-size
assumption beyond being a finite field. A later source-interface lemma
specializes this to the active centered v8 Taylor features. -/
theorem exact_reduced_coefficient_rank (e : Fin q ≃ K) (f : J → MvPolynomial E K) :
    (residueEvaluationMatrix e f).rank=(reducedCoefficientMatrix f).rank := by
  rw [evaluates_matrix e f]
  exact rank_after_invertible_left (fieldReceiver (E:=E) e) (fieldEvaluation e)
    (reducedCoefficientMatrix f) (receives_exactly e)

#print axioms redExp_lt
#print axioms reduced_power
#print axioms tensor_composition
#print axioms tensor_identity
#print axioms receives_exactly
#print axioms evaluate_after_reduction
#print axioms exact_reduced_coefficient_rank
end
end V8CapacitySpecialResidue

