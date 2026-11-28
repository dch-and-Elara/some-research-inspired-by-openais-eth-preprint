import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

/-! Ordered bordered minors. The order is extended by one tagged index,
so the identity works even for repeated original row or column labels. -/
namespace J3R60
open Matrix

/-- The top-left Schur determinant formula, by square block LDU. This is
the proof of Mathlib's `Matrix.det_fromBlocks₁₁` (SchurComplement.lean;
Bentkamp, Wieser, Avigad, Commelin), kept local because the pinned sparse
offline build lacks an object for that file. -/
private theorem schur_det {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (A : Matrix K K ℚ) (B : Matrix K V ℚ)
    (C : Matrix V K ℚ) (D : Matrix V V ℚ) [Invertible A] :
    (fromBlocks A B C D).det = A.det * (D - C * ⅟A * B).det := by
  have hLDU : fromBlocks A B C D =
      fromBlocks 1 0 (C * ⅟A) 1 * fromBlocks A 0 0 (D - C * ⅟A * B) *
        fromBlocks 1 (⅟A * B) 0 1 := by
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, invOf_mul_self, Matrix.mul_invOf_cancel_left,
      Matrix.mul_assoc, add_sub_cancel]
  rw [hLDU, det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁,
    det_fromBlocks_zero₁₂, det_one, det_one, one_mul, one_mul, mul_one]

def push {K α : Type*} (f : K → α) (a : α) : K ⊕ Unit → α :=
  Sum.elim f (fun _ => a)

def window {K I J α : Type*} (X : I → J → α)
    (pr : K → I) (pc : K → J) : Matrix K K α :=
  fun i j => X (pr i) (pc j)

def bordered {K I J α : Type*} [CommRing α] [Fintype K] [DecidableEq K]
    (X : I → J → α) (pr : K → I) (pc : K → J) (r : I) (c : J) : α :=
  (window X (push pr r) (push pc c)).det

abbrev Two := Unit ⊕ Unit

def twoIndex : Fin 2 ≃ Two where
  toFun i := if i.val = 0 then .inl () else .inr ()
  invFun s := s.elim (fun _ => 0) (fun _ => 1)
  left_inv i := by fin_cases i <;> decide
  right_inv s := by rcases s with (_|_) <;> rfl

theorem det_two (A : Matrix Two Two ℚ) :
    A.det = A (.inl ()) (.inl ()) * A (.inr ()) (.inr ()) -
      A (.inl ()) (.inr ()) * A (.inr ()) (.inl ()) := by
  rw [← Matrix.det_submatrix_equiv_self twoIndex A, Matrix.det_fin_two]
  rfl

theorem ordered_bordered_identity {K I J : Type*} [Fintype K] [DecidableEq K]
    (X : I → J → ℚ) (pr : K → I) (pc : K → J) (p r : I) (q c : J)
    (hp : (window X pr pc).det ≠ 0) :
    bordered X pr pc p q * bordered X pr pc r c -
        bordered X pr pc r q * bordered X pr pc p c =
      (window X pr pc).det * bordered X (push pr p) (push pc q) r c := by
  let rsel : Two → I := Sum.elim (fun _ => p) (fun _ => r)
  let csel : Two → J := Sum.elim (fun _ => q) (fun _ => c)
  let A := window X pr pc
  let B : Matrix K Two ℚ := fun i j => X (pr i) (csel j)
  let C : Matrix Two K ℚ := fun i j => X (rsel i) (pc j)
  let D : Matrix Two Two ℚ := fun i j => X (rsel i) (csel j)
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hp)
  let S := D - C * ⅟A * B
  have hBorder (i j : Two) : bordered X pr pc (rsel i) (csel j) = A.det * S i j := by
    let b : Matrix K Unit ℚ := fun k _ => B k j
    let c' : Matrix Unit K ℚ := fun _ k => C i k
    let d : Matrix Unit Unit ℚ := fun _ _ => D i j
    have hx : window X (push pr (rsel i)) (push pc (csel j)) =
        Matrix.fromBlocks A b c' d := by
      ext k l
      rcases k with (_|_) <;> rcases l with (_|_) <;> rfl
    rw [bordered, hx, schur_det, Matrix.det_unique (d - c' * ⅟A * b)]
    rfl
  have hDouble : bordered X (push pr p) (push pc q) r c = A.det * S.det := by
    let e := Equiv.sumAssoc K Unit Unit
    have hx : window X (push (push pr p) r) (push (push pc q) c) =
        (Matrix.fromBlocks A B C D).submatrix e e := by
      ext i j
      rcases i with ((_ | _) | _) <;> rcases j with ((_ | _) | _) <;> rfl
    rw [bordered, hx, Matrix.det_submatrix_equiv_self, schur_det]
  change bordered X pr pc (rsel (.inl ())) (csel (.inl ())) *
      bordered X pr pc (rsel (.inr ())) (csel (.inr ())) -
        bordered X pr pc (rsel (.inr ())) (csel (.inl ())) *
          bordered X pr pc (rsel (.inl ())) (csel (.inr ())) =
      A.det * bordered X (push pr p) (push pc q) r c
  rw [hBorder,hBorder,hBorder,hBorder,hDouble,det_two]
  ring

/-- The actual cross update is the adjacent ordered border divided by the
old leading determinant, with no divisions or signs supplied externally. -/
theorem ordered_bordered_div {K I J : Type*} [Fintype K] [DecidableEq K]
    (X : I → J → ℚ) (pr : K → I) (pc : K → J) (p r : I) (q c : J)
    (hp : (window X pr pc).det ≠ 0) :
    (bordered X pr pc p q * bordered X pr pc r c -
      bordered X pr pc r q * bordered X pr pc p c) / (window X pr pc).det =
      bordered X (push pr p) (push pc q) r c := by
  apply (div_eq_iff hp).mpr
  rw [ordered_bordered_identity X pr pc p r q c hp, mul_comm]

#print axioms det_two
#print axioms ordered_bordered_identity
#print axioms ordered_bordered_div

end J3R60
