import P5H4Sharp
import P5H4Degree

/-! For the same square polynomial, H.6 has three generally distinct exact
equality cases, rather than one unidentified sum-of-width estimate. -/
namespace P5H4
open Polynomial Matrix RankBudget
open scoped BigOperators Classical

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem allocated_divides (s : Finset K) (p : K[X]) :
    allocated s (fun t => rootMultiplicity t p) ∣ p := by
  unfold allocated
  refine Finset.prod_dvd_of_coprime (fun t _ u _ h => ?_) fun t _ => ?_
  · exact ((pairwise_coprime_X_sub_C (s:=fun x : K => x) Function.injective_id) h).pow
  · exact pow_rootMultiplicity_dvd p t

/-- There is no unseen degree iff the whole nonzero polynomial is exactly
a nonzero constant times the product of all its observed root powers. -/
theorem fully_sampled_iff (s : Finset K) (p : K[X]) (hp : p ≠ 0) :
    (∑ t ∈ s, rootMultiplicity t p) = p.natDegree ↔
      ∃ c : K, c ≠ 0 ∧ p = C c * allocated s (fun t => rootMultiplicity t p) := by
  let g := allocated s (fun t => rootMultiplicity t p)
  have hg : g ≠ 0 := (allocated_monic _ _).ne_zero
  have hdeg : g.natDegree = ∑ t ∈ s, rootMultiplicity t p := allocated_degree _ _
  constructor
  · intro h
    obtain ⟨q,hq⟩ := allocated_divides s p
    change p = g * q at hq
    have hqn : q ≠ 0 := by
      intro hz
      exact hp (by simpa [hz] using hq)
    have he : p.natDegree = g.natDegree + q.natDegree :=
      (congrArg natDegree hq).trans (natDegree_mul hg hqn)
    have hqc := eq_C_of_natDegree_eq_zero (p:=q) (show q.natDegree = 0 by omega)
    have hnon : q.coeff 0 ≠ 0 := by
      intro hn
      exact hqn (hqc.trans (by simp [hn]))
    refine ⟨q.coeff 0,hnon,?_⟩
    change p = C (q.coeff 0) * g
    rw [hq, ← hqc, mul_comm]
  · rintro ⟨c,hc,he⟩
    change p = C c * g at he
    have hu : C c ≠ (0 : K[X]) := C_ne_zero.mpr hc
    calc
      _ = g.natDegree := hdeg.symm
      _ = (C c * g).natDegree := by rw [natDegree_mul hu hg, natDegree_C, zero_add]
      _ = _ := congrArg natDegree he.symm

theorem rootMultiplicity_polynomial_unit (u : K[X]) (hu : IsUnit u) (t : K) :
    rootMultiplicity t u = 0 := by
  calc
    _ = rootMultiplicity t (C (u.coeff 0)) := congrArg _ (eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hu))
    _ = _ := rootMultiplicity_C _ t

theorem diagonal_orders_det (P U V : Matrix n n K[X]) (a : n → K[X]) (t : K)
    (hp : P.det ≠ 0) (hu : IsUnit U) (hv : IsUnit V) (hm : U * P * V = diagonal a) :
    rootMultiplicity t P.det = ∑ i, rootMultiplicity t (a i) := by
  have h := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
  have hdu := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hdv := (Matrix.isUnit_iff_isUnit_det _).mp hv
  have ha := (diagonalDegree P U V a hp hu hv hm).1
  calc
    _ = rootMultiplicity t (U.det * P.det * V.det) := by
      rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hdu.ne_zero hp) hdv.ne_zero),
          rootMultiplicity_mul (mul_ne_zero hdu.ne_zero hp),
          rootMultiplicity_polynomial_unit _ hdu, rootMultiplicity_polynomial_unit _ hdv,
          zero_add, add_zero]
    _ = _ := (congrArg (rootMultiplicity t) h).trans (rootMultiplicity_prod _ _ (fun i _ => ha i) t)

theorem diag_clipped_profile (P U V : Matrix n n K[X]) (a : n → K[X])
    (hp : P.det ≠ 0) (hu : IsUnit U) (hv : IsUnit V) (hm : U * P * V = diagonal a)
    (t : K) (k : ℕ) :
    Fintype.card n * k - jetLength P t k = ∑ i, min k (rootMultiplicity t (a i)) := by
  have ha := (diagonalDegree P U V a hp hu hv hm).1
  rw [← jetLength_unimodular P U V hu hv t k, hm, jetLength_diagonal _ ha]
  have hsum : (∑ i, (k - min k (rootMultiplicity t (a i)))) +
      ∑ i, min k (rootMultiplicity t (a i)) = Fintype.card n * k := by
    rw [← Finset.sum_add_distrib]
    simp [Nat.sub_add_cancel (min_le_left _ _)]
  omega

/-- One simultaneous diagonalization gives the local profile, determinant
orders and exact first two equality cases in (H.6). No choice of diagonal
basis separately at each truncation or observation is needed. -/
theorem faithful_square_profile (P : Matrix n n K[X]) (hp : P.det ≠ 0) :
    ∃ (U V : Matrix n n K[X]) (a : n → K[X]),
      IsUnit U ∧ IsUnit V ∧ U * P * V = diagonal a ∧ (∀ i, a i ≠ 0) ∧
      (∀ t k, Fintype.card n * k - jetLength P t k = ∑ i, min k (rootMultiplicity t (a i))) ∧
      (∀ t, rootMultiplicity t P.det = ∑ i, rootMultiplicity t (a i)) ∧
      (∀ (s : Finset K) (k : K → ℕ),
        (∑ t ∈ s, (Fintype.card n * k t - jetLength P t (k t))) =
          (∑ t ∈ s, rootMultiplicity t P.det) ↔
          ∀ t ∈ s, ∀ i, rootMultiplicity t (a i) ≤ k t) ∧
      (∀ s : Finset K,
        (∑ t ∈ s, rootMultiplicity t P.det) = P.det.natDegree ↔
        ∃ c : K, c ≠ 0 ∧ P.det = C c * allocated s (fun t => rootMultiplicity t P.det)) := by
  obtain ⟨U,V,a,hu,hv,hm⟩ := polyDiagonalize P hp
  have hc := diag_clipped_profile P U V a hp hu hv hm
  have hd := diagonal_orders_det P U V a
  refine ⟨U,V,a,hu,hv,hm,(diagonalDegree P U V a hp hu hv hm).1,hc,?_,?_,?_⟩
  · exact fun t => hd t hp hu hv hm
  · intro s k
    simp only [hc, fun t => hd t hp hu hv hm]
    exact clipped_eq_iff s k (fun t i => rootMultiplicity t (a i))
  · exact fun s => fully_sampled_iff s P.det hp

#print axioms fully_sampled_iff
#print axioms diagonal_orders_det
#print axioms diag_clipped_profile
#print axioms faithful_square_profile
end P5H4
