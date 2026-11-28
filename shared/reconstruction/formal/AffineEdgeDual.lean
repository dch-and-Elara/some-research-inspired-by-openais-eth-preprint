import AffineEdgeModel
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Ring

open Polynomial
open scoped Polynomial BigOperators

namespace AffineEdge

noncomputable section

variable {q : ℕ} {ι F A : Type*} [Field F] [Fintype A] [DecidableEq A]

/-- Lemma 4's affine test, written in the basis `1, X`. -/
def AffineCondition (sites : Fin q → F) (C : ι → PairWord q A → F) : Prop :=
  ∀ u (f g : PairWord q A → F),
    (∀ j, ∑ v, C j v * f v = 0) →
    (∀ j, ∑ v, C j v * g v = 0) →
    (∀ t v, v.1 t = u.2 t → f v + sites t * g v = 0) →
    f u = 0

variable [Fintype ι]

/-- The finite coefficient system for one row of the reconstruction. Over
the rationals these are linear equations with rational coefficients. -/
def RowSystem (sites : Fin q → F) (C : ι → PairWord q A → F) (u : PairWord q A)
    (c₀ c₁ : ι → F) (local₀ : Fin q → PairWord q A → F) : Prop :=
  (∀ t v, v.1 t ≠ u.2 t → local₀ t v = 0) ∧
  (∀ v, (∑ j, c₀ j * C j v) + (∑ t, local₀ t v) = if u = v then 1 else 0) ∧
  (∀ v, (∑ j, c₁ j * C j v) + (∑ t, sites t * local₀ t v) = 0)

theorem rowSystem_of_affine {sites : Fin q → F} {C : ι → PairWord q A → F}
    (ha : AffineCondition sites C) (u : PairWord q A) :
    ∃ c₀ c₁ local₀, RowSystem sites C u c₀ c₁ local₀ := by
  classical
  let W := PairWord q A
  let V := (W → F) × (W → F)
  let e₀ (v : W) : V →ₗ[F] F := (LinearMap.proj v).comp (LinearMap.fst F _ _)
  let e₁ (v : W) : V →ₗ[F] F := (LinearMap.proj v).comp (LinearMap.snd F _ _)
  let L : ((ι × Bool) ⊕ (Fin q × W)) → V →ₗ[F] F :=
    Sum.elim (fun p => ∑ v, C p.1 v • (if p.2 then e₁ v else e₀ v))
      (fun p => if p.2.1 p.1 = u.2 p.1 then e₀ p.2 + sites p.1 • e₁ p.2 else 0)
  have hker : (⨅ i, LinearMap.ker (L i)) ≤ LinearMap.ker (e₀ u) := by
    intro fg hfg
    have he (i) : L i fg = 0 := (Submodule.mem_iInf _).mp hfg i
    apply ha u fg.1 fg.2
    · intro j
      simpa [L, e₀, LinearMap.sum_apply, smul_eq_mul] using he (.inl (j, false))
    · intro j
      simpa [L, e₁, LinearMap.sum_apply, smul_eq_mul] using he (.inl (j, true))
    · intro t v h
      simpa [L, h, e₀, e₁, smul_eq_mul] using he (.inr (t, v))
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (mem_span_of_iInf_ker_le_ker hker)
  let c₀ (j : ι) := z (.inl (j, false))
  let c₁ (j : ι) := z (.inl (j, true))
  let local₀ (t : Fin q) (v : W) := if v.1 t = u.2 t then z (.inr (t,v)) else 0
  have hz' (f g : W → F) :
      (∑ j, (c₁ j * (∑ v, C j v * g v) + c₀ j * (∑ v, C j v * f v))) +
        (∑ t, ∑ v, local₀ t v * (f v + sites t * g v)) = f u := by
    have h₀ (j : ι) : L (.inl (j,false)) (f,g) = ∑ v, C j v * f v := by
      simp [L, e₀, LinearMap.sum_apply, smul_eq_mul]
      rfl
    have h₁ (j : ι) : L (.inl (j,true)) (f,g) = ∑ v, C j v * g v := by
      simp [L, e₁, LinearMap.sum_apply, smul_eq_mul]
      rfl
    have hl (t : Fin q) (v : W) :
        z (.inr (t,v)) * L (.inr (t,v)) (f,g) = local₀ t v * (f v + sites t * g v) := by
      by_cases h : v.1 t = u.2 t
      · simp only [L, local₀, Sum.elim_inr, if_pos h, LinearMap.add_apply,
          LinearMap.smul_apply, smul_eq_mul]
        rfl
      · simp [L, local₀, h]
    have he : e₀ u (f,g) = f u := rfl
    simpa only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Fintype.sum_bool, h₀, h₁, hl, he, c₀, c₁] using
      LinearMap.congr_fun hz (f,g)
  have hsingle (v : W) (f : W → F) :
      (∑ w, f w * (Pi.single v 1 : W → F) w) = f v := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw
      simp [hw]
    · simp
  have hC (v : W) (j : ι) :
      (∑ w, C j w * (Pi.single v 1 : W → F) w) = C j v :=
    hsingle v (C j)
  refine ⟨c₀, c₁, local₀, ?_, ?_, ?_⟩
  · intro t v hv
    simp [local₀, hv]
  · intro v
    have h := hz' (Pi.single v 1) 0
    have hl (t : Fin q) :
        (∑ w, local₀ t w * (Pi.single v 1 : W → F) w) = local₀ t v :=
      hsingle v (local₀ t)
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, add_zero, hC, hl] at h
    simpa [Pi.single_apply] using h
  · intro v
    have h := hz' 0 (Pi.single v 1)
    have hlocal (t : Fin q) :
        (∑ w, local₀ t w * (sites t * (Pi.single v 1 : W → F) w)) = sites t * local₀ t v := by
      simp only [mul_left_comm (local₀ t _) (sites t), ← Finset.mul_sum, hsingle v (local₀ t)]
    simpa only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, add_zero, hlocal,
      hC] using h

private def nodeProduct (sites : Fin q → F) (t : Fin q) : F[X] :=
  ∏ s ∈ Finset.univ.erase t, (X - Polynomial.C (sites s))

private theorem nodeProduct_degree (sites : Fin q → F) (t : Fin q) :
    (nodeProduct sites t).natDegree = q-1 := by
  unfold nodeProduct
  rw [natDegree_prod_of_monic _ _ (fun s _ => monic_X_sub_C (sites s))]
  simp [Finset.card_erase_of_mem (Finset.mem_univ t)]

private theorem nodeProduct_coeff (sites : Fin q → F) (t : Fin q) :
    (nodeProduct sites t).coeff (q-1) = 1 := by
  rw [← nodeProduct_degree sites t]
  exact monic_prod_of_monic _ _ (fun s _ => monic_X_sub_C (sites s))

private def normalizer (sites : Fin q → F) : F :=
  (-(∏ t, -sites t))⁻¹

private theorem normalizer_eval_zero (sites : Fin q → F) (hn : ∀ t, sites t ≠ 0) (t : Fin q) :
    normalizer sites * (sites t * (nodeProduct sites t).eval 0) = 1 := by
  have he := Finset.prod_erase_mul (f := fun s => -sites s) Finset.univ (Finset.mem_univ t)
  have hp : (∏ s, -sites s) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
    intro s _
    exact neg_ne_zero.mpr (hn s))
  have he' : sites t * (∏ s ∈ Finset.univ.erase t, -sites s) = -(∏ s, -sites s) := by
    rw [← he, mul_neg, neg_neg, mul_comm]
  simp only [nodeProduct, eval_prod, eval_sub, eval_X, eval_C, zero_sub]
  rw [he', normalizer, inv_mul_cancel₀ (neg_ne_zero.mpr hp)]

/-- A solution of the row system gives the actual entrywise polynomials. -/
def reconstructEntry (sites : Fin q → F) (C : ι → PairWord q A → F)
    (c₀ c₁ : ι → F) (local₀ : Fin q → PairWord q A → F) (v : PairWord q A) : F[X] :=
  Polynomial.C (∑ j, c₀ j * C j v) + Polynomial.C (normalizer sites) *
    (Polynomial.C (∑ j, c₁ j * C j v) * X^(q-1) +
      ∑ t, Polynomial.C (sites t * local₀ t v) * nodeProduct sites t)

omit [Fintype A] in
theorem reconstructEntry_degree {sites : Fin q → F} {C : ι → PairWord q A → F}
    {u : PairWord q A} {c₀ c₁ : ι → F} {local₀ : Fin q → PairWord q A → F}
    (hq : 2 ≤ q) (h : RowSystem sites C u c₀ c₁ local₀) (v : PairWord q A) :
    (reconstructEntry sites C c₀ c₁ local₀ v).natDegree ≤ q-2 := by
  let G := Polynomial.C (∑ j, c₁ j * C j v) * X^(q-1) +
      ∑ t, Polynomial.C (sites t * local₀ t v) * nodeProduct sites t
  have hG : G.natDegree ≤ q-1 := by
    apply (natDegree_add_le _ _).trans
    refine max_le ((natDegree_C_mul_le _ _).trans (by simp)) ?_
    apply natDegree_sum_le_of_forall_le
    intro t _
    exact (natDegree_C_mul_le _ _).trans_eq (nodeProduct_degree sites t)
  have hcoeff : G.coeff (q-1) = 0 := by
    simpa only [G, coeff_add, coeff_C_mul, nodeProduct_coeff, finset_sum_coeff, coeff_X_pow,
      if_true, mul_one] using h.2.2 v
  have hg : G.natDegree ≤ q-2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases he : n = q-1
    · simpa [he] using hcoeff
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  change (Polynomial.C _ + Polynomial.C _ * G).natDegree ≤ _
  exact (natDegree_add_le _ _).trans (max_le (by rw [natDegree_C]; omega)
    ((natDegree_C_mul_le _ _).trans hg))

omit [Fintype A] in
theorem reconstructEntry_zero {sites : Fin q → F} {C : ι → PairWord q A → F}
    {u : PairWord q A} {c₀ c₁ : ι → F} {local₀ : Fin q → PairWord q A → F}
    (hq : 2 ≤ q) (hn : ∀ t, sites t ≠ 0) (h : RowSystem sites C u c₀ c₁ local₀)
    (v : PairWord q A) :
    (reconstructEntry sites C c₀ c₁ local₀ v).eval 0 = if u = v then 1 else 0 := by
  simp only [reconstructEntry, eval_add, eval_C, eval_mul, eval_pow, eval_X, eval_finset_sum,
    zero_pow (show q-1 ≠ 0 by omega), mul_zero, zero_add, Finset.mul_sum]
  have he (t : Fin q) :
      normalizer sites * (sites t * local₀ t v * (nodeProduct sites t).eval 0) = local₀ t v := by
    calc
      _ = local₀ t v * (normalizer sites * (sites t * (nodeProduct sites t).eval 0)) := by ring
      _ = _ := by rw [normalizer_eval_zero sites hn t, mul_one]
  simp_rw [he]
  exact h.2.1 v

omit [Fintype A] in
theorem reconstructEntry_local {sites : Fin q → F} {C : ι → PairWord q A → F}
    {u : PairWord q A} {c₀ c₁ : ι → F} {local₀ : Fin q → PairWord q A → F}
    (h : RowSystem sites C u c₀ c₁ local₀) (t : Fin q) (v : PairWord q A)
    (hv : v.1 t ≠ u.2 t) :
    (reconstructEntry sites C c₀ c₁ local₀ v).eval (sites t) =
      (∑ j, c₀ j * C j v) + (normalizer sites * (sites t)^(q-1)) * ∑ j, c₁ j * C j v := by
  have hz : (∑ s, sites s * local₀ s v * (nodeProduct sites s).eval (sites t)) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : t = s
    · subst s
      simp [h.1 t v hv]
    · have he : (nodeProduct sites s).eval (sites t) = 0 := by
        rw [nodeProduct, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ _⟩) (by simp)
      simp [he]
  simp only [reconstructEntry, eval_add, eval_C, eval_mul, eval_pow, eval_X,
    eval_finset_sum, hz, add_zero]
  ring

/-- Turn supplied solutions of the finite systems into a recovery matrix.
The witnesses can, for example, be supplied by rational Gaussian elimination. -/
theorem reconstruct_matrix_of_rowSystems {sites : Fin q → F} {C : ι → PairWord q A → F}
    (hq : 2 ≤ q) (hn : ∀ t, sites t ≠ 0)
    {c₀ c₁ : PairWord q A → ι → F} {L : PairWord q A → Fin q → PairWord q A → F}
    (h : ∀ u, RowSystem sites C u (c₀ u) (c₁ u) (L u)) :
    PairedCondition sites C (q-2) (fun u => reconstructEntry sites C (c₀ u) (c₁ u) (L u)) := by
  classical
  let P u := reconstructEntry sites C (c₀ u) (c₁ u) (L u)
  refine ⟨fun u v => reconstructEntry_degree hq (h u) v,
    fun u v => reconstructEntry_zero hq hn (h u) v, ?_⟩
  intro u t z hk hl
  change (∑ v, (P u v).eval (sites t) * z v) = 0
  let c := normalizer sites * (sites t)^(q-1)
  have he (v : PairWord q A) :
      (P u v).eval (sites t) * z v =
        ((∑ j, c₀ u j * C j v) + c * ∑ j, c₁ u j * C j v) * z v := by
    by_cases hv : v.1 t = u.2 t
    · simp [hl v hv]
    · rw [reconstructEntry_local (h u) t v hv]
  have hs (a : ι → F) : (∑ v, (∑ j, a j * C j v) * z v) = 0 := by
    simp only [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hk]
  simp only [he, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hs,
    mul_zero, add_zero]

theorem paired_of_affine {sites : Fin q → F} {C : ι → PairWord q A → F}
    (hq : 2 ≤ q) (hn : ∀ t, sites t ≠ 0) (ha : AffineCondition sites C) :
    ∃ P, PairedCondition sites C (q-2) P := by
  classical
  choose c₀ c₁ L h using rowSystem_of_affine ha
  exact ⟨_, reconstruct_matrix_of_rowSystems hq hn h⟩

/-- The full fixed-matrix equivalence of Lemma 4. -/
theorem paired_iff_affine {sites : Fin q → F} {C : ι → PairWord q A → F}
    (hq : 2 ≤ q) (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    (∃ P, PairedCondition sites C (q-2) P) ↔ AffineCondition sites C :=
  ⟨fun ⟨_, h⟩ => affine_test_of_paired hq hi h, paired_of_affine hq hn⟩

/-- The original formulation of the affine test with polynomial entries. -/
def PolynomialAffineCondition (sites : Fin q → F) (C : ι → PairWord q A → F) : Prop :=
  ∀ u (h : PairWord q A → F[X]), (∀ v, (h v).natDegree ≤ 1) →
    (∀ j, (∑ v, Polynomial.C (C j v) * h v) = 0) →
    (∀ t v, v.1 t = u.2 t → (h v).eval (sites t) = 0) →
    (h u).eval 0 = 0

omit [DecidableEq A] [Fintype ι] in
theorem affineCondition_iff_polynomial {sites : Fin q → F} {C : ι → PairWord q A → F} :
    AffineCondition sites C ↔ PolynomialAffineCondition sites C := by
  constructor
  · intro ha u h hd hk hl
    let f (v : PairWord q A) := (h v).coeff 0
    let g (v : PairWord q A) := (h v).coeff 1
    have hrepr (v : PairWord q A) : h v = Polynomial.C (f v) + X * Polynomial.C (g v) := by
      have hdv : (h v).divX.natDegree = 0 := by
        rw [natDegree_divX_eq_natDegree_tsub_one]
        exact Nat.sub_eq_zero_of_le (hd v)
      have he : (h v).divX = Polynomial.C (g v) := by
        rw [eq_C_of_natDegree_eq_zero hdv]
        simp [g, coeff_divX]
      rw [add_comm, ← he]
      exact (X_mul_divX_add (h v)).symm
    have hf (j : ι) : (∑ v, C j v * f v) = 0 := by
      simpa only [finset_sum_coeff, coeff_C_mul, coeff_zero, f] using
        congrArg (fun p : F[X] => p.coeff 0) (hk j)
    have hg (j : ι) : (∑ v, C j v * g v) = 0 := by
      simpa only [finset_sum_coeff, coeff_C_mul, coeff_zero, g] using
        congrArg (fun p : F[X] => p.coeff 1) (hk j)
    have ht (t : Fin q) (v : PairWord q A) (hv : v.1 t = u.2 t) :
        f v + sites t * g v = 0 := by
      simpa only [hrepr v, eval_add, eval_mul, eval_C, eval_X] using hl t v hv
    simpa only [f, coeff_zero_eq_eval_zero] using ha u f g hf hg ht
  · intro hp u f g hf hg hl
    let h (v : PairWord q A) := Polynomial.C (f v) + X * Polynomial.C (g v)
    have hd (v : PairWord q A) : (h v).natDegree ≤ 1 := by
      apply (natDegree_add_le _ _).trans
      exact max_le (by simp) (natDegree_mul_le.trans (by simp))
    have hk (j : ι) : (∑ v, Polynomial.C (C j v) * h v) = 0 := by
      simp only [h, mul_add, Finset.sum_add_distrib, ← map_mul,
        mul_left_comm (Polynomial.C (C j _)) X, ← Finset.mul_sum, ← map_sum, hf, hg,
        map_zero, mul_zero, add_zero]
    have ht (t : Fin q) (v : PairWord q A) (hv : v.1 t = u.2 t) :
        (h v).eval (sites t) = 0 := by
      simpa only [h, eval_add, eval_mul, eval_C, eval_X] using hl t v hv
    simpa only [h, eval_add, eval_mul, eval_C, eval_X, zero_mul, add_zero] using hp u h hd hk ht

theorem paired_iff_polynomial_affine {sites : Fin q → F} {C : ι → PairWord q A → F}
    (hq : 2 ≤ q) (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    (∃ P, PairedCondition sites C (q-2) P) ↔ PolynomialAffineCondition sites C :=
  (paired_iff_affine hq hi hn).trans affineCondition_iff_polynomial

end
end AffineEdge
