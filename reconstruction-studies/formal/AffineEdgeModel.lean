import AffineEdgeCount
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

open Polynomial
open scoped Polynomial BigOperators

namespace AffineEdge

abbrev PairWord (q : ℕ) (A : Type*) := (Fin q → A) × (Fin q → A)
abbrev Word (q : ℕ) := PairWord q Bool

/-- The paper's common-kernel condition on the physical ordered pairs.
At slot `t`, output `u` knows input `v` exactly when `v.1 t = u.2 t`. -/
def PairedCondition {q : ℕ} {ι F A : Type*} [Field F] [Fintype A] [DecidableEq A]
    (sites : Fin q → F) (C : ι → PairWord q A → F) (d : ℕ)
    (P : PairWord q A → PairWord q A → F[X]) : Prop :=
  (∀ u v, (P u v).natDegree ≤ d) ∧
  (∀ u v, (P u v).eval 0 = if u = v then 1 else 0) ∧
  ∀ u t (z : PairWord q A → F), (∀ j, ∑ v, C j v * z v = 0) →
    (∀ v, v.1 t = u.2 t → z v = 0) →
    ∑ v, (P u v).eval (sites t) * z v = 0

/-- The necessary affine half of the paper's dual criterion follows directly
by multiplying one reconstruction row by an affine kernel vector. -/
theorem affine_test_of_paired {q : ℕ} {ι F A : Type*} [Field F] [Fintype A] [DecidableEq A]
    {sites : Fin q → F} {C : ι → PairWord q A → F}
    {P : PairWord q A → PairWord q A → F[X]}
    (hq : 2 ≤ q) (hinj : Function.Injective sites)
    (hp : PairedCondition sites C (q-2) P)
    (u : PairWord q A) (f g : PairWord q A → F)
    (hf : ∀ j, ∑ v, C j v * f v = 0) (hg : ∀ j, ∑ v, C j v * g v = 0)
    (hlocal : ∀ t v, v.1 t = u.2 t → f v + sites t * g v = 0) :
    f u = 0 := by
  classical
  let H (v : PairWord q A) : F[X] := Polynomial.C (f v) + X * Polynomial.C (g v)
  let R : F[X] := ∑ v, P u v * H v
  have hdH (v : PairWord q A) : (H v).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    exact max_le (by simp) (natDegree_mul_le.trans (by simp))
  have hdR : R.natDegree < Fintype.card (Fin q) := by
    have hd : R.natDegree ≤ (q-2)+1 := by
      apply natDegree_sum_le_of_forall_le
      intro v _
      exact natDegree_mul_le.trans (Nat.add_le_add (hp.1 u v) (hdH v))
    simp only [Fintype.card_fin]
    omega
  have hroot (t : Fin q) : R.eval (sites t) = 0 := by
    have hk (j : ι) : (∑ v, C j v * (f v + sites t * g v)) = 0 := by
      simp only [mul_add, Finset.sum_add_distrib, mul_left_comm (C j _) (sites t),
        ← Finset.mul_sum, hf, hg, mul_zero, add_zero]
    simpa only [R, H, eval_finset_sum, eval_add, eval_mul, eval_C, eval_X] using
      hp.2.2 u t (fun v => f v + sites t * g v) hk (hlocal t)
  have hz := eq_zero_of_natDegree_lt_card_of_eval_eq_zero R hinj hroot hdR
  have h0 := congrArg (Polynomial.eval (0 : F)) hz
  simpa [R, H, eval_finset_sum, hp.2.1, ite_mul] using h0

end AffineEdge
