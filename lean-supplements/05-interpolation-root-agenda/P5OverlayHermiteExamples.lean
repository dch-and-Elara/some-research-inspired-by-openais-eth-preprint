import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The concrete failure tests of §2.3. Each matrix, anchor and
residue below is evaluated in the ring used in the example. -/
namespace Paper5.HermiteExamples
open Polynomial Matrix
open scoped Classical Polynomial

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 4000000

noncomputable section

def mod8Example : (ZMod 8)[X] := X^2-1

theorem four_noncomaximal_roots_at_degree_two :
    mod8Example.natDegree=2 ∧ IsUnit (mod8Example.eval 0) ∧
      ∃ s : Finset (ZMod 8), s.card=4 ∧ ∀ t∈s,mod8Example.eval t=0 := by
  letI : Nontrivial (ZMod 8) := ⟨⟨0,1,by decide⟩⟩
  let s : Finset (ZMod 8) := {1,3,5,7}
  refine ⟨?_,?_,s,by decide,?_⟩
  · unfold mod8Example
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · rw [Polynomial.natDegree_X_pow]
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_one]
      decide
  · rw [show mod8Example.eval 0=(-1:ZMod 8) by simp [mod8Example]]
    exact (isUnit_one : IsUnit (1 : ZMod 8)).neg
  · intro t ht
    change t∈({1,3,5,7} : Finset (ZMod 8)) at ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl|rfl|rfl|rfl <;>
      simp only [mod8Example,eval_sub,eval_pow,eval_X,eval_one] <;> decide

/-- The actual right Lagrange cardinal at centers 0 and 2^p. -/
def closeRightCardinal (p : ℕ) : ℚ[X] := C (((2 : ℚ)^p)⁻¹)*X

theorem close_centers_need_one_more_bit (p : ℕ) :
    let t : ℤ := (2:ℤ)^p
    let A : ℤ[X] := X
    A.eval 0=0 ∧ A.eval t=t ∧ A.eval 1=1 ∧
    ((A.eval t : ℤ) : ZMod (2^p))=0 ∧
    (closeRightCardinal p).eval 0=0 ∧ (closeRightCardinal p).eval (t:ℚ)=1 ∧
    (closeRightCardinal p).eval 1=((2:ℚ)^p)⁻¹ ∧
    padicValRat 2 ((closeRightCardinal p).eval 1)=-(p:ℤ) ∧
    (0 : ZMod 2)≠1 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have nz : (2:ℚ)^p≠0 := pow_ne_zero _ (by norm_num)
  have ht : (((2:ℤ)^p : ℤ):ℚ)=(2:ℚ)^p := by norm_cast
  have vp : padicValRat 2 ((2:ℚ)^p)=(p:ℤ) := by
    rw [padicValRat.pow (q:=(2:ℚ)) (by norm_num)]
    have vtwo : padicValRat 2 (2:ℚ)=1 := padicValRat.self (p:=2) (by decide)
    rw [vtwo,mul_one]
  dsimp only
  refine ⟨by simp,by simp,by simp,?_,by simp [closeRightCardinal],?_,by simp [closeRightCardinal],?_,by decide⟩
  · rw [Polynomial.eval_X]
    have he : (2:ℤ)^p = ((2^p:ℕ):ℤ) := by simp
    rw [he,Int.cast_natCast]
    exact ZMod.natCast_self (2^p)
  · simp only [closeRightCardinal,eval_mul,eval_C,eval_X,ht]
    exact inv_mul_cancel₀ nz
  · simp only [closeRightCardinal,eval_mul,eval_C,eval_X,mul_one,padicValRat.inv,vp]

def productLift : Matrix (Fin 2) (Fin 2) ℤ := !![1,2;2,4]

def canonicalReduction : Matrix (Fin 2) (Fin 2) ℤ := productLift.map (fun x=>x%3)

theorem strict_rank_gain_of_canonical_mod_three :
    (productLift.map (Int.cast : ℤ→ℚ)).rank≤1 ∧
    canonicalReduction.det=(-3:ℤ) ∧
    (canonicalReduction.map (Int.cast : ℤ→ℚ)).rank=2 ∧
    (canonicalReduction.map (Int.cast : ℤ→ZMod 3))=
      (productLift.map (Int.cast : ℤ→ZMod 3)) := by
  have old : productLift.map (Int.cast : ℤ→ℚ)=
      Matrix.vecMulVec ![1,2] (![1,2]:Fin 2→ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [productLift,Matrix.map_apply,Matrix.vecMulVec]
  have canon : canonicalReduction=!![(1:ℤ),2;2,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have neq : (canonicalReduction.map (Int.cast : ℤ→ℚ)).det≠0 := by
    rw [canon, Matrix.det_fin_two]
    norm_num [Matrix.map_apply]
  refine ⟨?_,?_,?_,?_⟩
  · rw [old]
    exact Matrix.rank_vecMulVec_le _ _
  · rw [canon,Matrix.det_fin_two]
    decide
  · let B := canonicalReduction.map (Int.cast : ℤ→ℚ)
    have h := Matrix.rank_mul_eq_right_of_isUnit_det B (1 : Matrix (Fin 2) (Fin 2) ℚ)
      (isUnit_iff_ne_zero.mpr neq)
    simpa [B] using h
  · ext i j
    fin_cases i <;> fin_cases j <;> decide

#print axioms four_noncomaximal_roots_at_degree_two
#print axioms close_centers_need_one_more_bit
#print axioms strict_rank_gain_of_canonical_mod_three
end
end Paper5.HermiteExamples
