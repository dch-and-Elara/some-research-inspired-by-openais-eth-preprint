import S7Decoder

namespace S7
open Finset Polynomial
open scoped BigOperators
noncomputable section
variable {K I : Type*} [Field K]

def CoeffBound (v : AddValuation K (WithTop ℤ)) (c : WithTop ℤ) (f : K[X]) : Prop :=
  ∀ j, c ≤ v (f.coeff j)

variable (v : AddValuation K (WithTop ℤ))

theorem valuation_sum_bound {A : Type*} (s : Finset A) (f : A → K) (a : WithTop ℤ)
    (h : ∀ j ∈ s, a ≤ v (f j)) : a ≤ v (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj]
    exact (le_min (h j (mem_insert_self _ _)) (ih fun i hi => h i (mem_insert_of_mem hi))).trans
      (v.map_add _ _)

theorem bound_sum {A : Type*} (s : Finset A) (f : A → K[X]) (a : WithTop ℤ)
    (h : ∀ j ∈ s, CoeffBound v a (f j)) : CoeffBound v a (∑ j ∈ s, f j) := by
  intro j
  rw [finset_sum_coeff]
  exact valuation_sum_bound v _ _ _ fun i hi => h i hi j

theorem bound_mul {a b : WithTop ℤ} {f g : K[X]} (hf : CoeffBound v a f)
    (hg : CoeffBound v b g) : CoeffBound v (a+b) (f*g) := by
  intro j
  rw [coeff_mul]
  apply valuation_sum_bound
  intro i _
  rw [v.map_mul]
  exact add_le_add (hf _) (hg _)

theorem bound_one : CoeffBound v 0 (1 : K[X]) := by
  intro j
  by_cases h : j = 0 <;> simp [coeff_one, h]

theorem bound_pow {a : WithTop ℤ} {f : K[X]} (hf : CoeffBound v a f) (n : ℕ) :
    CoeffBound v (n • a) (f^n) := by
  induction n with
  | zero => simpa using bound_one v
  | succ n ih => simpa only [pow_succ, succ_nsmul] using bound_mul v ih hf

theorem bound_neg {a : WithTop ℤ} {f : K[X]} (hf : CoeffBound v a f) : CoeffBound v a (-f) := by
  intro j
  simpa using hf j

theorem bound_add {a : WithTop ℤ} {f g : K[X]} (hf : CoeffBound v a f) (hg : CoeffBound v a g) :
    CoeffBound v a (f+g) := fun j => by
  rw [coeff_add]
  exact (le_min (hf j) (hg j)).trans (v.map_add _ _)

theorem bound_weaken {a b : WithTop ℤ} {f : K[X]} (h : a ≤ b)
    (hf : CoeffBound v b f) : CoeffBound v a f := fun j => h.trans (hf j)

theorem bound_C (z : K) : CoeffBound v (v z) (C z) := by
  intro j
  by_cases hj : j = 0 <;> simp [coeff_C, hj]

theorem bound_X : CoeffBound v 0 (X : K[X]) := by
  intro j
  by_cases hj : j = 1 <;> simp [coeff_X, hj, eq_comm]

theorem bound_prod {A : Type*} (s : Finset A) (f : A → K[X])
    (h : ∀ j ∈ s, CoeffBound v (v ((f j).eval 0)) (f j)) :
    CoeffBound v (v ((∏ j ∈ s, f j).eval 0)) (∏ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bound_one v
  | insert j s hj ih =>
    rw [prod_insert hj, eval_mul, v.map_mul]
    exact bound_mul v (h j (mem_insert_self _ _)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem cardinal_bound [Fintype I] [DecidableEq I] (x : I → K) (q : I → ℕ)
    (hv : ∀ s, v (x s) ≤ 0) (t : I) :
    CoeffBound v (v ((cardinal x q t).eval 0)) (cardinal x q t) := by
  unfold cardinal
  apply bound_prod
  intro s _
  rw [eval_pow, v.map_pow]
  apply bound_pow
  rw [eval_mul, eval_C, eval_sub, eval_X, eval_C, zero_sub, v.map_mul, v.map_neg]
  exact bound_mul v (bound_C v _) (by
    rw [sub_eq_add_neg]
    exact bound_add v (bound_weaken v (hv s) (bound_X v)) (bound_neg v (bound_C v _)))

theorem integral_prod {A : Type*} (s : Finset A) (f : A → K[X])
    (h : ∀ j ∈ s, CoeffBound v 0 (f j)) : CoeffBound v 0 (∏ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bound_one v
  | insert j s hj ih =>
    rw [prod_insert hj]
    simpa only [zero_add] using bound_mul v (h j (mem_insert_self _ _))
      (ih fun i hi => h i (mem_insert_of_mem hi))

theorem inverse_bound [Fintype I] [DecidableEq I] (x : I → K)
    (hx : Function.Injective x) (q : I → ℕ)
    (hdiff : ∀ t s, t ≠ s → 0 ≤ v ((x t-x s)⁻¹)) (t : I) :
    CoeffBound v 0 (geometricInverse (q t) (localFactor x q t)) := by
  have hf : CoeffBound v 0 (localFactor x q t) := by
    rw [localFactor_linearProduct x hx]
    apply integral_prod
    intro s hs
    have h := hdiff t s (Ne.symm (mem_erase.mp hs).1)
    have hmul : CoeffBound v 0 (C ((x t-x s)⁻¹)*X) := by
      simpa only [zero_add] using bound_mul v (bound_weaken v h (bound_C v _)) (bound_X v)
    simpa only [nsmul_zero] using bound_pow v (bound_add v (bound_one v) hmul) (q s)
  apply bound_sum
  intro j _
  rw [sub_eq_add_neg]
  simpa only [nsmul_zero] using bound_pow v (bound_add v (bound_one v) (bound_neg v hf)) j

theorem subst_trunc_bound (x : K) (g c : ℤ) (hg : 0 ≤ g) (hx : v x = ↑(-g))
    (q : ℕ) (f : K[X]) (hf : CoeffBound v (↑c) f) :
    CoeffBound v (↑(c - (q-1 : ℕ)*g : ℤ)) (subst (X-C x) (trunc q f)) := by
  have hshift : CoeffBound v (↑(-g)) (X-C x) := by
    rw [sub_eq_add_neg]
    have he := bound_C v x
    rw [hx] at he
    exact bound_add v (bound_weaken v (by norm_cast; omega) (bound_X v)) (bound_neg v he)
  unfold trunc
  rw [map_sum]
  apply bound_sum
  intro i hi
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, subst_X, subst_C]
  have hh := bound_pow v hshift i
  rw [← WithTop.coe_nsmul, nsmul_eq_mul] at hh
  have hmul := bound_mul v (bound_weaken v (hf i) (bound_C v (f.coeff i))) hh
  rw [← WithTop.coe_add] at hmul
  apply bound_weaken v _ hmul
  rw [WithTop.coe_le_coe]
  have hi' : (i:ℤ) ≤ ((q-1 : ℕ):ℤ) := by have := mem_range.mp hi; omega
  nlinarith only [mul_le_mul_of_nonneg_right hi' hg]

variable [Fintype I] [DecidableEq I]

/-- Every transfer-matrix entry has the denominator bound used in P.1. -/
theorem error_bound (x : I → K) (hx : Function.Injective x) (q gap : I → ℕ)
    (c : I → ℤ) (hval : ∀ t, v (x t) = ↑(-(gap t : ℤ)))
    (hc : ∀ t, v ((cardinal x q t).eval 0) = ↑(c t))
    (hdiff : ∀ t s, t ≠ s → 0 ≤ v ((x t-x s)⁻¹))
    (t : I) (j k : ℕ) :
    CoeffBound v (↑(c t-(↑(q t-1)+k)*(gap t) : ℤ)) (errorPolynomial x q t j k) := by
  have hg : (0:ℤ) ≤ gap t := by positivity
  have hshift : CoeffBound v (↑(-(gap t:ℤ))) (X+C (x t)) := by
    have h := bound_C v (x t)
    rw [hval] at h
    exact bound_add v (bound_weaken v (by norm_cast; omega) (bound_X v)) h
  have hp := bound_pow v hshift k
  rw [← WithTop.coe_nsmul, nsmul_eq_mul] at hp
  have hX := bound_pow v (bound_X v) j
  simp only [nsmul_zero] at hX
  have hinner := bound_mul v (bound_mul v hX hp) (inverse_bound v x hx q hdiff t)
  simp only [zero_add, add_zero] at hinner
  have hlocal := subst_trunc_bound v (x t) (gap t) (k * -(gap t:ℤ)) hg (hval t) (q t) _ hinner
  have hcard := cardinal_bound v x q (fun s => by rw [hval]; norm_cast; omega) t
  rw [hc] at hcard
  have h := bound_mul v hcard hlocal
  rw [← WithTop.coe_add] at h
  convert h using 2
  ring

theorem highestJet_valuation (x : I → K) (hx : Function.Injective x) (q gap : I → ℕ)
    (c : I → ℤ) (hval : ∀ t, v (x t) = ↑(-(gap t : ℤ)))
    (hc : ∀ t, v ((cardinal x q t).eval 0) = ↑(c t))
    (t : I) (hq : 0 < q t) (k : ℕ) :
    v ((errorPolynomial x q t (q t-1) k).coeff 0) =
      ↑(c t-(↑(q t-1)+k)*(gap t) : ℤ) := by
  rw [highestJet_constant x hx q t hq, v.map_mul, v.map_mul, v.map_pow, v.map_pow,
      v.map_neg, hc, hval, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
      ← WithTop.coe_add, ← WithTop.coe_add]
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- Finite coordinate changes with each retained coefficient independently chosen. -/
def Certified (v : AddValuation K (WithTop ℤ)) (x : I → K) (q : I → ℕ)
    (P : I → ℕ) (p b : ℕ) : Prop :=
  ∀ e : (Σ t, Fin (q t)) → K, (∀ j, (↑(P j.1 : ℤ) : WithTop ℤ) ≤ v (e j)) →
    ∀ k l : Fin b, (↑(p : ℤ) : WithTop ℤ) ≤ v
      (∑ j, e j * (errorPolynomial x q j.1 j.2 k).coeff l)

/-- P.1. The converse is witnessed by one highest-jet error of size 2^P. -/
theorem certified_iff_criterion (x : I → K) (hx : Function.Injective x)
    (q gap : I → ℕ) (c : I → ℤ) (P : I → ℕ) (p b : ℕ)
    (hq : ∀ t, 0 < q t) (hb : 0 < b) (h₂ : v (2 : K) = 1)
    (hval : ∀ t, v (x t) = ↑(-(gap t : ℤ)))
    (hc : ∀ t, v ((cardinal x q t).eval 0) = ↑(c t))
    (hdiff : ∀ t s, t ≠ s → 0 ≤ v ((x t-x s)⁻¹)) :
    Certified v x q P p b ↔ WindowCriterion gap (fun t => (P t : ℤ)-p+c t) q b := by
  classical
  have hpw (n : ℕ) : v ((2:K)^n) = (↑(n:ℤ) : WithTop ℤ) := by
    rw [v.map_pow, h₂, ← WithTop.coe_one, ← WithTop.coe_nsmul]
    simp
  constructor
  · intro h t
    let j : Σ t, Fin (q t) := ⟨t,⟨q t-1, by have := hq t; omega⟩⟩
    let e : (Σ t, Fin (q t)) → K := fun i => if i = j then 2^(P t) else 0
    have he (i : Σ t, Fin (q t)) : (↑(P i.1 : ℤ) : WithTop ℤ) ≤ v (e i) := by
      by_cases hi : i = j
      · subst i
        simp [e, hpw, j]
      · simp [e, hi]
    have htest := h e he ⟨b-1, by omega⟩ ⟨0,hb⟩
    rw [sum_eq_single j] at htest
    · simp only [e, if_pos rfl] at htest
      change (↑(p : ℤ) : WithTop ℤ) ≤
        v (2^(P t) * (errorPolynomial x q t (q t-1) (b-1)).coeff 0) at htest
      rw [v.map_mul, hpw, highestJet_valuation v x hx q gap c hval hc t (hq t),
        ← WithTop.coe_add, WithTop.coe_le_coe] at htest
      have heq : (↑(q t-1) : ℤ)+(↑(b-1):ℤ) = (b:ℤ)+q t-2 := by
        have := hq t
        omega
      rw [heq] at htest
      change ((b : ℤ)+q t-2)*gap t ≤ _
      dsimp
      linarith only [htest]
    · intro i _ hi
      simp [e, hi]
    · simp
  · intro h e he k l
    apply valuation_sum_bound v
    intro j _
    rw [v.map_mul]
    have hh := add_le_add (he j) (error_bound v x hx q gap c hval hc hdiff j.1 j.2 k l)
    refine le_trans ?_ hh
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    have hq' := hq j.1
    have hk := k.isLt
    have hk' : (↑(q j.1-1):ℤ)+(k.val:ℤ) ≤ (b:ℤ)+q j.1-2 := by omega
    have hg : (0:ℤ) ≤ gap j.1 := by positivity
    have hcrit := h j.1
    dsimp at hcrit
    nlinarith only [hcrit, mul_le_mul_of_nonneg_right hk' hg]

end
end S7
