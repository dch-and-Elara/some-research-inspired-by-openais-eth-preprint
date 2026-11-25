import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The finite quadratic sign-maximization step of Bang's argument.
The rounding polytope and the probabilistic matching are not formalized here. -/

namespace BangCore

open scoped BigOperators

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I]

def bitSign (b : Bool) : ℚ := if b then 1 else -1

theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

def qnorm (w : E → ℚ) : ℚ := ∑ e, w e ^ 2

def dot (v w : E → ℚ) : ℚ := ∑ e, v e * w e

def signedTotal (v : I → E → ℚ) (eps : I → Bool) (e : E) : ℚ :=
  ∑ i, bitSign (eps i) * v i e

theorem flip_quadratic (w v : E → ℚ) (r : ℚ) (hr : r ^ 2 = 1) :
    qnorm (fun e => w e - 2 * r * v e) =
      qnorm w - 4 * r * dot v w + 4 * qnorm v := by
  have hpoint (e : E) :
      (w e - 2 * r * v e) ^ 2 =
        w e ^ 2 - 4 * r * (v e * w e) + 4 * v e ^ 2 := by
    calc
      _ = w e ^ 2 - 4 * r * (v e * w e) + 4 * r ^ 2 * v e ^ 2 := by ring
      _ = _ := by rw [hr]; ring
  simp only [qnorm, hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, dot]

omit [Fintype E] in
theorem flip_identity (v : I → E → ℚ) (eps : I → Bool) (i : I) :
    signedTotal v (Function.update eps i (!(eps i))) =
      fun e => signedTotal v eps e - 2 * bitSign (eps i) * v i e := by
  funext e
  have hpoint (j : I) :
      bitSign ((Function.update eps i (!(eps i))) j) * v j e =
        bitSign (eps j) * v j e +
          if j = i then -2 * bitSign (eps i) * v i e else 0 := by
    by_cases hj : j = i
    · subst j
      cases eps i <;> simp [Function.update, bitSign] <;> ring
    · simp [hj]
  simp only [signedTotal, hpoint, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem exists_simultaneous_signed_dot (v : I → E → ℚ) :
    ∃ eps : I → Bool, ∀ i,
      qnorm (v i) ≤ bitSign (eps i) * dot (v i) (signedTotal v eps) := by
  classical
  obtain ⟨eps, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (I → Bool)) (fun eps => qnorm (signedTotal v eps))
    Finset.univ_nonempty
  refine ⟨eps, ?_⟩
  intro i
  have h := hmax (Function.update eps i (!(eps i))) (Finset.mem_univ _)
  rw [flip_identity, flip_quadratic _ _ _ (bitSign_sq (eps i))] at h
  linarith

#print axioms bitSign_sq
#print axioms flip_quadratic
#print axioms flip_identity
#print axioms exists_simultaneous_signed_dot

end BangCore
