import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-! Literal coefficient-first convolution and the true powers of the
truncated shift, in slot order (jet exponent, matrix coordinate). -/
namespace Paper5.HermiteGeneric
open Matrix
open scoped BigOperators Kronecker Classical

variable {R U V : Type*} [CommSemiring R]

def shiftMatrix (R : Type*) [CommSemiring R] (k j : ℕ) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun r l => if r.val=l.val+j then 1 else 0

@[simp] theorem shiftMatrix_apply (k j : ℕ) (r l : Fin k) :
    shiftMatrix R k j r l = if r.val=l.val+j then 1 else 0 := rfl

@[simp] theorem shift_zero (k : ℕ) : shiftMatrix R k 0=1 := by
  ext r l
  by_cases h : r=l
  · subst l
    simp [shiftMatrix]
  · have hv : r.val≠l.val := fun he=>h (Fin.ext he)
    simp [shiftMatrix,hv,Matrix.one_apply_ne h]

theorem shift_mul (k u v : ℕ) : shiftMatrix R k u * shiftMatrix R k v=shiftMatrix R k (u+v) := by
  ext r l
  rw [Matrix.mul_apply]
  by_cases h : r.val=l.val+(u+v)
  · let m : Fin k := ⟨l.val+v,by have hh:= r.isLt; omega⟩
    have hm : m.val=l.val+v := rfl
    have hr : r.val=m.val+u := by omega
    rw [Finset.sum_eq_single m]
    · simp only [shiftMatrix_apply,if_pos hr,if_pos hm,if_pos h,one_mul]
    · intro x _ hxm
      have hn : x.val≠l.val+v := fun h'=>hxm (Fin.ext (h'.trans hm.symm))
      simp [hn]
    · simp
  · rw [shiftMatrix_apply,if_neg h]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : m.val=l.val+v
    · have hr : r.val≠m.val+u := by omega
      simp [hr]
    · simp [hm]

theorem shift_power (k j : ℕ) : (shiftMatrix R k 1)^j=shiftMatrix R k j := by
  induction j with
  | zero => simp
  | succ j h => rw [pow_succ,h,shift_mul]

noncomputable def convolution {k : ℕ} (C : Fin k→Matrix U V R) :
    Matrix (Fin k × U) (Fin k × V) R :=
  ∑ j : Fin k,shiftMatrix R k j.val ⊗ₖ C j

theorem convolution_apply {k : ℕ} (C : Fin k→Matrix U V R)
    (r l : Fin k) (u : U) (v : V) :
    convolution C (r,u) (l,v) =
      if _h : l.val≤r.val then C ⟨r.val-l.val,lt_of_le_of_lt (Nat.sub_le _ _) r.isLt⟩ u v
      else 0 := by
  rw [convolution,Matrix.sum_apply]
  simp only [Matrix.kronecker_apply,shiftMatrix_apply]
  by_cases h : l.val≤r.val
  · let j : Fin k := ⟨r.val-l.val,(Nat.sub_le _ _).trans_lt r.isLt⟩
    have hj : r.val=l.val+j.val := by dsimp [j]; omega
    rw [dif_pos h,Finset.sum_eq_single j]
    · rw [if_pos hj,one_mul]
    · intro j' _ h'
      have hne : r.val≠l.val+j'.val := by
        intro hh
        apply h'
        apply Fin.ext
        change j'.val = r.val-l.val
        omega
      simp [hne]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have hn : r.val≠l.val+j.val := by omega
    simp [hn]

theorem convolution_map {S : Type*} [CommSemiring S] {k : ℕ}
    (f : R→+*S) (C : Fin k→Matrix U V R) :
    (convolution C).map f = convolution (fun j=>(C j).map f) := by
  apply Matrix.ext
  rintro ⟨r,u⟩ ⟨l,v⟩
  rw [Matrix.map_apply,convolution_apply,convolution_apply]
  split <;> simp

#print axioms shift_zero
#print axioms shift_mul
#print axioms shift_power
#print axioms convolution_apply
#print axioms convolution_map
end Paper5.HermiteGeneric
