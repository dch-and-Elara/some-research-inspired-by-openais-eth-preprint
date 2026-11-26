import P5MainBalanceM6Origin
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.FinCases
import Mathlib.Data.ZMod.Basic

/-! Only the precision actually used by the M.6 terminal rank test:
integrality and exact reduction modulo two of the printed sparse lift.
No theorem here claims the stronger full p_ell congruence. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 Polynomial
open scoped BigOperators Classical Polynomial

noncomputable def idempotentPrinted (ell : ℕ) : ℤ[X] :=
  (1-X)^ell * ∑ j∈Finset.range ell,C ((ell+j-1).choose j:ℤ)*X^j

noncomputable def quad : ℤ[X] := X*(X-1)

theorem quad_monic : quad.Monic := by
  have h := monic_X_sub_C (1:ℤ)
  exact monic_X.mul (by simpa only [C_1] using h)

theorem idempotent_zero (ell : ℕ) (he : 0<ell) :
    (idempotentPrinted ell).eval 0=1 := by
  unfold idempotentPrinted
  simp only [eval_mul,eval_finset_sum,eval_pow,eval_sub,eval_one,eval_X,eval_C,
    sub_zero,one_pow,one_mul]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr he)]
  · simp
  · intro j _ hj
    simp [zero_pow hj]

theorem idempotent_one (ell : ℕ) (he : 0<ell) :
    (idempotentPrinted ell).eval 1=0 := by
  simp [idempotentPrinted,zero_pow (Nat.ne_of_gt he)]

noncomputable def printedE (ell j : ℕ) : ℤ[X] :=
  ((fun p : ℤ[X]=>p /ₘ quad)^[j]) (idempotentPrinted ell) %ₘ quad

theorem printed_e_zero_zero (ell : ℕ) (he : 0<ell) : (printedE ell 0).eval 0=1 := by
  unfold printedE
  rw [Function.iterate_zero_apply,modByMonic_eq_sub_mul_div _ quad_monic]
  simp [quad,idempotent_zero ell he]

theorem printed_e_zero_one (ell : ℕ) (he : 0<ell) : (printedE ell 0).eval 1=0 := by
  unfold printedE
  rw [Function.iterate_zero_apply,modByMonic_eq_sub_mul_div _ quad_monic]
  simp [quad,idempotent_one ell he]

private theorem zmod_two_cases (b : ZMod 2) : b=0 ∨ b=1 := by
  have hb := ZMod.val_lt b
  have h : b.val=0 ∨ b.val=1 := by omega
  rcases h with h|h
  · left; rw [←ZMod.natCast_zmod_val b,h,Nat.cast_zero]
  · right; rw [←ZMod.natCast_zmod_val b,h,Nat.cast_one]

theorem integer_quad_residue (y : ℤ) : ((y*(y-1):ℤ):ZMod 2)=0 := by
  push_cast
  rcases zmod_two_cases (y:ZMod 2) with h|h <;> simp [h]

theorem constant_lift_mod_two (ell : ℕ) (he : 0<ell) (y : ℤ) :
    (((printedE ell 0).eval y:ℤ):ZMod 2)=
      (if (y:ZMod 2)=0 then 1 else 0) := by
  let m := Int.castRingHom (ZMod 2)
  have h (u : ℤ) : ((printedE ell 0).map m).eval (m u)=m ((printedE ell 0).eval u) := by
    rw [eval_map,eval₂_hom]
  change m ((printedE ell 0).eval y) = (if m y=0 then 1 else 0)
  rw [←h y]
  rcases zmod_two_cases (m y) with H|H
  · rw [H,if_pos rfl,←map_zero m,h 0,printed_e_zero_zero ell he,map_one]
  · rw [H,if_neg one_ne_zero,←map_one m,h 1,printed_e_zero_one ell he,map_zero]

noncomputable def integerSparseFactor (ell : ℕ) (y : ℤ) : ℤ[X] :=
  ∑ a : Fin ell,monomial a.val ((printedE ell a).eval y*(y*(y-1))^a.val)

set_option maxHeartbeats 5500000 in
theorem sparse_factor_mod_two (ell : ℕ) (he : 0<ell) (y : ℤ) :
    (integerSparseFactor ell y).map (Int.castRingHom (ZMod 2))=
      C (if (y:ZMod 2)=0 then 1 else 0) := by
  unfold integerSparseFactor
  rw [Polynomial.map_sum]
  simp_rw [Polynomial.map_monomial,map_mul,map_pow]
  rw [Finset.sum_eq_single (⟨0,he⟩:Fin ell)]
  · simp only [pow_zero,mul_one,monomial_zero_left]
    exact congrArg C (constant_lift_mod_two ell he y)
  · intro i _ hi
    have h : 0<(i:ℕ) := Nat.pos_of_ne_zero (fun hz=>hi (Fin.ext hz))
    change monomial i.val ((((printedE ell i).eval y:ℤ):ZMod 2) * (((y*(y-1):ℤ):ZMod 2)^i.val))=0
    rw [integer_quad_residue,zero_pow h.ne',mul_zero,monomial_zero_right]
  · simp

#print axioms idempotent_zero
#print axioms idempotent_one
#print axioms printed_e_zero_zero
#print axioms printed_e_zero_one
#print axioms integer_quad_residue
#print axioms constant_lift_mod_two
#print axioms sparse_factor_mod_two
end P5MainBalance.M6.Sparse
