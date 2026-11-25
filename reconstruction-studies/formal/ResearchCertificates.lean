import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Lean.Elab.Tactic.Omega

/-!
Kernel-checked finite algebraic core of the symmetry-free certificate.
This file does NOT formalize the binomial dimension count or asymptotics.
Only the usual logical axioms of Lean/Mathlib are used.
-/

open scoped BigOperators
open Polynomial

namespace Reconstruction

noncomputable section

variable {V I M : Type*} [Fintype V] [Fintype I] [Fintype M] [DecidableEq V]

def contract (P : V → V → ℚ[X]) (h g : V → ℚ[X]) : ℚ[X] :=
  ∑ u, ∑ v, g u * P u v * h v

def Locality (C : M → V → ℚ) (P : V → V → ℚ[X])
    (t : I → ℚ) (slice : I → V → Prop) : Prop :=
  ∀ i (x : V → ℚ),
    (∀ a, ∑ v, C a v * x v = 0) →
    (∀ v, ¬slice i v → x v = 0) →
    ∀ u, slice i u → ∑ v, (P u v).eval (t i) * x v = 0

theorem contract_eval (P : V → V → ℚ[X]) (h g : V → ℚ[X]) (x : ℚ) :
    (contract P h g).eval x =
      ∑ u, (g u).eval x * (∑ v, (P u v).eval x * (h v).eval x) := by
  classical
  simp only [contract, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Finset.mul_sum, mul_assoc]

theorem contract_eval_zero (P : V → V → ℚ[X]) (h g : V → ℚ[X])
    (hP : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0) :
    (contract P h g).eval 0 = ∑ u, (g u).eval 0 * (h u).eval 0 := by
  classical
  rw [contract_eval]
  simp [hP]

theorem contract_vanishes
    (C : M → V → ℚ) (P : V → V → ℚ[X]) (t : I → ℚ)
    (slice : I → V → Prop) (h g : V → ℚ[X])
    (hloc : Locality C P t slice)
    (hker : ∀ a, (∑ v, Polynomial.C (C a v) * h v) = 0)
    (hsupp : ∀ i v, ¬slice i v → (h v).eval (t i) = 0)
    (gsupp : ∀ i v, ¬slice i v → (g v).eval (t i) = 0) :
    ∀ i, (contract P h g).eval (t i) = 0 := by
  classical
  intro i
  rw [contract_eval]
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hs : slice i u
  · have hz : ∀ a, ∑ v, C a v * (h v).eval (t i) = 0 := by
      intro a
      have he := congrArg (fun f : ℚ[X] => f.eval (t i)) (hker a)
      simpa only [Polynomial.eval_finset_sum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_zero] using he
    rw [hloc i (fun v => (h v).eval (t i)) hz (hsupp i) u hs]
    simp
  · rw [gsupp i u hs]
    simp

theorem contract_degree (P : V → V → ℚ[X]) (h g : V → ℚ[X])
    (d j l : ℕ) (hP : ∀ u v, (P u v).natDegree ≤ d)
    (hh : ∀ v, (h v).natDegree ≤ j)
    (hg : ∀ v, (g v).natDegree ≤ l) :
    (contract P h g).natDegree ≤ d + j + l := by
  classical
  unfold contract
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro v hv
  calc
    (g u * P u v * h v).natDegree
        ≤ (g u * P u v).natDegree + (h v).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (g u).natDegree + (P u v).natDegree + (h v).natDegree :=
      Nat.add_le_add_right Polynomial.natDegree_mul_le _
    _ ≤ d + j + l := by have := hP u v; have := hh v; have := hg u; omega

theorem bilinear_certificate
    (C : M → V → ℚ) (P : V → V → ℚ[X]) (t : I → ℚ)
    (slice : I → V → Prop) (h g : V → ℚ[X])
    (d j l : ℕ)
    (ht : Function.Injective t)
    (hP0 : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hloc : Locality C P t slice)
    (hker : ∀ a, (∑ v, Polynomial.C (C a v) * h v) = 0)
    (hsupp : ∀ i v, ¬slice i v → (h v).eval (t i) = 0)
    (gsupp : ∀ i v, ¬slice i v → (g v).eval (t i) = 0)
    (hPd : ∀ u v, (P u v).natDegree ≤ d)
    (hhd : ∀ v, (h v).natDegree ≤ j)
    (hgd : ∀ v, (g v).natDegree ≤ l)
    (hdeg : d + j + l < Fintype.card I) :
    ∑ v, (g v).eval 0 * (h v).eval 0 = 0 := by
  have hp : contract P h g = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ht
      (contract_vanishes C P t slice h g hloc hker hsupp gsupp)
      (lt_of_le_of_lt (contract_degree P h g d j l hPd hhd hgd) hdeg)
  rw [← contract_eval_zero P h g hP0, hp]
  simp

theorem square_certificate
    (C : M → V → ℚ) (P : V → V → ℚ[X]) (t : I → ℚ)
    (slice : I → V → Prop) (h : V → ℚ[X]) (d k : ℕ)
    (ht : Function.Injective t)
    (hP0 : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hloc : Locality C P t slice)
    (hker : ∀ a, (∑ v, Polynomial.C (C a v) * h v) = 0)
    (hsupp : ∀ i v, ¬slice i v → (h v).eval (t i) = 0)
    (hPd : ∀ u v, (P u v).natDegree ≤ d)
    (hhd : ∀ v, (h v).natDegree ≤ k)
    (hdeg : d + 2 * k < Fintype.card I) :
    ∀ v, (h v).eval 0 = 0 := by
  classical
  have hz : ∑ v, (h v).eval 0 * (h v).eval 0 = 0 :=
    bilinear_certificate C P t slice h h d k k ht hP0 hloc hker hsupp hsupp
      hPd hhd hhd (by omega)
  exact fun v => (Finset.sum_mul_self_eq_zero_iff Finset.univ
    (fun v => (h v).eval 0)).mp hz v (Finset.mem_univ v)

#print axioms bilinear_certificate
#print axioms square_certificate

end
end Reconstruction
