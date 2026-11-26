import P5A2Powers
import Mathlib.LinearAlgebra.Lagrange

/-! Ordinary interpolation of unreduced representatives of all groups,
as in v7 lines 598–608 and 1317–1322. Only the ordinary polynomials
are evaluated at scalar nodes. -/
namespace Paper5.GenericReadout
open Polynomial
open scoped BigOperators Polynomial Classical

variable {K : Type*} [Field K]

noncomputable def uniRep (k : ℕ) (x : P5A2.Trunc K k) : K[X] :=
  AdjoinRoot.modByMonicHom (monic_X_pow k) x

theorem uniRep_mk (k : ℕ) (x : P5A2.Trunc K k) :
    AdjoinRoot.mk ((X:K[X])^k) (uniRep k x)=x :=
  AdjoinRoot.mk_leftInverse (monic_X_pow k) x

theorem uniRep_degree (k : ℕ) (x : P5A2.Trunc K k) : (uniRep k x).natDegree≤k-1 := by
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
  unfold uniRep
  rw [AdjoinRoot.modByMonicHom_mk]
  have h := degree_modByMonic_lt p (monic_X_pow k)
  rw [degree_X_pow] at h
  by_cases h0 : p %ₘ (X:K[X])^k=0
  · simp [h0]
  · have h' := (natDegree_lt_iff_degree_lt h0).mpr h
    omega

noncomputable def lagrange {d : ℕ} (x : Fin (d+1)→K) (i : Fin (d+1)) : K[X] :=
  Lagrange.basis Finset.univ x i

theorem ordinary_interpolate {d : ℕ} (x : Fin (d+1)→K) (hx : Function.Injective x)
    (p : K[X]) (hp : p.natDegree≤d) :
    p=∑ i,C (p.eval (x i))*lagrange x i := by
  have h : p.degree < (↑((Finset.univ : Finset (Fin (d+1))).card):WithBot ℕ) := by
    rw [Finset.card_univ,Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hp))
  exact Lagrange.eq_interpolate hx.injOn h

theorem no_quotient_evaluation (k : ℕ) (a : K) (ha : a≠0)
    (e : P5A2.Trunc K k→+*K) :
    ¬ ∀ p : K[X],e (AdjoinRoot.mk ((X:K[X])^k) p)=p.eval a := by
  intro h
  have hx := h ((X:K[X])^k)
  rw [AdjoinRoot.mk_self,map_zero,Polynomial.eval_pow,Polynomial.eval_X] at hx
  exact (pow_ne_zero k ha) hx.symm

variable {G : Type*} [Fintype G]

theorem ordinary_product_degree (d : ℕ) (p : G→K[X]) (hd : ∀ g,(p g).natDegree≤d) :
    (∏ g,p g).natDegree≤Fintype.card G*d := by
  refine (natDegree_prod_le Finset.univ p).trans ?_
  calc
    _ ≤ ∑ _g : G,d := Finset.sum_le_sum (fun g _=>hd g)
    _ = _ := by simp

set_option maxHeartbeats 11000000 in
theorem scalarize_ordinary_univariate (k : ℕ) (read : P5A2.Trunc K k→ₗ[K]K)
    (x : Fin (Fintype.card G*(k-1)+1)→K) (hx : Function.Injective x)
    (u : G→P5A2.Trunc K k) :
    read (∏ g,u g) =
      ∑ i,read (AdjoinRoot.mk ((X:K[X])^k) (lagrange x i)) *
        ∏ g,(uniRep k (u g)).eval (x i) := by
  let p (g : G) := uniRep k (u g)
  let Q := AdjoinRoot.mk ((X:K[X])^k)
  have hp : (∏ g,p g).natDegree≤Fintype.card G*(k-1) :=
    ordinary_product_degree _ p (fun g=>uniRep_degree k (u g))
  calc
    _ = read (Q (∏g,p g)) := by rw [map_prod Q]; simp only [p,Q,uniRep_mk]
    _ = _ := by
      rw [ordinary_interpolate x hx _ hp,map_sum,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      have hC (a : K) : Q (C a)=algebraMap K (P5A2.Trunc K k) a := rfl
      rw [hC,←Algebra.smul_def]
      change read ((∏g,p g).eval (x i) • Q (lagrange x i)) =
        read (Q (lagrange x i)) * ∏g,(p g).eval (x i)
      rw [map_smul,smul_eq_mul,mul_comm]
      congr 1
      exact map_prod (Polynomial.evalRingHom (x i)) _ _

#print axioms uniRep_mk
#print axioms uniRep_degree
#print axioms ordinary_interpolate
#print axioms no_quotient_evaluation
#print axioms ordinary_product_degree
#print axioms scalarize_ordinary_univariate
end Paper5.GenericReadout
