import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

open scoped BigOperators

namespace SharpDifference

section Alternants

variable {R σ : Type*} [CommRing R] [DecidableEq σ]

noncomputable def mergeVars (a b : σ) : MvPolynomial σ R →+* MvPolynomial σ R :=
  (MvPolynomial.rename fun j => if j = b then a else j).toRingHom

@[simp] theorem mergeVars_X (a b j : σ) :
    mergeVars (R := R) a b (MvPolynomial.X j) = MvPolynomial.X (if j = b then a else j) :=
  MvPolynomial.rename_X _ _

@[simp] theorem mergeVars_C (a b : σ) (r : R) :
    mergeVars a b (MvPolynomial.C r) = MvPolynomial.C r := MvPolynomial.rename_C _ _

noncomputable def gap (a b : σ) : MvPolynomial σ R := MvPolynomial.X b - MvPolynomial.X a

theorem gap_dvd_sub_merge (a b : σ) (p : MvPolynomial σ R) :
    gap a b ∣ p - mergeVars a b p := by
  let I : Ideal (MvPolynomial σ R) := Ideal.span {gap a b}
  let q := Ideal.Quotient.mk I
  have he : q (MvPolynomial.X b) = q (MvPolynomial.X a) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hq : q.comp (mergeVars (R := R) a b) = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply]
    · intro i
      simp only [RingHom.comp_apply, mergeVars_X]
      by_cases hi : i = b
      · subst i
        simp [he]
      · simp [hi]
  have hmem : p - mergeVars a b p ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, show q (mergeVars a b p) = q p from DFunLike.congr_fun hq p, sub_self]
  exact Ideal.mem_span_singleton.mp hmem

theorem gap_dvd_of_merge_eq_zero (a b : σ) (p : MvPolynomial σ R)
    (h : mergeVars a b p = 0) : gap a b ∣ p := by
  simpa only [h, sub_zero] using gap_dvd_sub_merge a b p

variable [IsDomain R] [LinearOrder σ]

theorem mergeVars_gap_ne_zero {a b u v : σ} (hab : a < b) (huv : u < v)
    (hpair : (u, v) ≠ (a, b)) :
    mergeVars (R := R) a b (gap u v) ≠ 0 := by
  simp only [gap, map_sub, mergeVars_X, sub_ne_zero, MvPolynomial.X_injective.ne_iff]
  by_cases h₁ : u = b <;> by_cases h₂ : v = b
  · subst u
    subst v
    exact (lt_irrefl _ huv).elim
  · subst u
    simp only [h₂, if_false]
    exact ne_of_gt (hab.trans huv)
  · subst v
    simp only [h₁, if_false]
    intro he
    subst u
    exact hpair rfl
  · simp [h₁, h₂, ne_of_gt huv]

/-- Remove all distinct pair factors by successive variable identifications. -/
theorem prod_gap_dvd_of_merges (s : Finset (σ × σ)) (p : MvPolynomial σ R)
    (hord : ∀ z ∈ s, z.1 < z.2)
    (hzero : ∀ z ∈ s, mergeVars z.1 z.2 p = 0) :
    (∏ z ∈ s, gap z.1 z.2) ∣ p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert z s hz ih =>
    have hzord := hord z (Finset.mem_insert_self _ _)
    obtain ⟨q, hq⟩ := ih
      (fun w hw => hord w (Finset.mem_insert_of_mem hw))
      (fun w hw => hzero w (Finset.mem_insert_of_mem hw))
    have hm := hzero z (Finset.mem_insert_self _ _)
    rw [hq, map_mul] at hm
    have hprod : mergeVars z.1 z.2 (∏ w ∈ s, gap w.1 w.2 : MvPolynomial σ R) ≠ 0 := by
      rw [map_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro w hw
      exact mergeVars_gap_ne_zero hzord (hord w (Finset.mem_insert_of_mem hw))
        (fun he => hz ((show w = z from he) ▸ hw))
    obtain ⟨q', hq'⟩ := gap_dvd_of_merge_eq_zero z.1 z.2 q
      ((mul_eq_zero.mp hm).resolve_left hprod)
    refine ⟨q', ?_⟩
    rw [hq, hq', Finset.prod_insert hz]
    ac_rfl

end Alternants

section Determinants

variable {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}

noncomputable def alternantMatrix (p : Fin k → Polynomial R) :
    Matrix (Fin k) (Fin k) (MvPolynomial (Fin k) R) :=
  Matrix.of fun i j => (p i).eval₂ MvPolynomial.C (MvPolynomial.X j)

noncomputable def symbolicV (k : ℕ) : MvPolynomial (Fin k) R :=
  (Matrix.vandermonde MvPolynomial.X).det

noncomputable def orderedPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter fun z => z.1 < z.2

omit [IsDomain R] in
theorem symbolicV_eq_prod (k : ℕ) :
    symbolicV (R := R) k = ∏ z ∈ orderedPairs k, gap z.1 z.2 := by
  rw [symbolicV, Matrix.det_vandermonde, orderedPairs]
  have hu : (Finset.univ : Finset (Fin k × Fin k)) = Finset.univ ×ˢ Finset.univ := by
    ext z
    simp
  rw [hu, Finset.prod_filter, Finset.prod_product]
  apply Finset.prod_congr rfl
  intro a _
  rw [← Finset.prod_filter]
  apply Finset.prod_congr
  · ext b
    simp
  · intro b _
    rfl

theorem symbolicV_dvd_alternant (p : Fin k → Polynomial R) :
    symbolicV (R := R) k ∣ (alternantMatrix p).det := by
  rw [symbolicV_eq_prod]
  apply prod_gap_dvd_of_merges
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · rintro ⟨a, b⟩ hab
    have hlt : a < b := (Finset.mem_filter.mp hab).2
    rw [RingHom.map_det]
    apply Matrix.det_zero_of_column_eq hlt.ne
    intro i
    simp [alternantMatrix, Polynomial.hom_eval₂, hlt.ne]


omit [IsDomain R] in
private theorem rename_alternant_det (p : Fin k → Polynomial R) (π : Equiv.Perm (Fin k)) :
    MvPolynomial.rename π (alternantMatrix p).det =
      (((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial (Fin k) R) * (alternantMatrix p).det := by
  rw [AlgHom.map_det]
  have hc : (MvPolynomial.rename (R := R) π).toRingHom.comp MvPolynomial.C =
      MvPolynomial.C := by
    apply RingHom.ext
    intro r
    exact MvPolynomial.rename_C _ _
  have hm : (alternantMatrix p).map (MvPolynomial.rename (R := R) π) =
      (alternantMatrix p).submatrix id π := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id_eq, alternantMatrix,
      Matrix.of_apply]
    change (MvPolynomial.rename (R := R) π).toRingHom ((p i).eval₂ MvPolynomial.C (MvPolynomial.X j)) = _
    rw [Polynomial.hom_eval₂, hc]
    congr 1
    exact MvPolynomial.rename_X π j
  change ((alternantMatrix p).map (MvPolynomial.rename (R := R) π)).det = _
  rw [hm, Matrix.det_permute']

omit [IsDomain R] in
private theorem rename_symbolicV (π : Equiv.Perm (Fin k)) :
    MvPolynomial.rename π (symbolicV (R := R) k) =
      (((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial (Fin k) R) * symbolicV k := by
  rw [symbolicV, AlgHom.map_det]
  have hm : (Matrix.vandermonde (MvPolynomial.X (R := R))).map
      (MvPolynomial.rename (R := R) π) =
      (Matrix.vandermonde (MvPolynomial.X (R := R))).submatrix π id := by
    apply Matrix.ext
    intro i j
    simp [Matrix.vandermonde_apply]
  change ((Matrix.vandermonde (MvPolynomial.X (R := R))).map (MvPolynomial.rename (R := R) π)).det = _
  rw [hm, Matrix.det_permute]

/-- Factor the alternating determinant over the coefficient ring, before evaluation. -/
theorem exists_symmetric_alternant_quotient (p : Fin k → Polynomial R) :
    ∃ Q : MvPolynomial (Fin k) R, (alternantMatrix p).det = symbolicV k * Q ∧
      ∀ π : Equiv.Perm (Fin k), MvPolynomial.rename π Q = Q := by
  obtain ⟨Q, hQ⟩ := symbolicV_dvd_alternant p
  refine ⟨Q, hQ, ?_⟩
  intro π
  have hv : symbolicV (R := R) k ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr MvPolynomial.X_injective
  let s : MvPolynomial (Fin k) R := ((Equiv.Perm.sign π : ℤˣ) : ℤ)
  have hs : s ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [s, h]
  apply mul_left_cancel₀ (mul_ne_zero hs hv)
  calc
    _ = MvPolynomial.rename π (alternantMatrix p).det := by
      rw [hQ, map_mul, rename_symbolicV]
    _ = _ := by rw [rename_alternant_det, hQ, mul_assoc]

omit [IsDomain R] in
theorem eval_alternant_det (p : Fin k → Polynomial R) (x : Fin k → R) :
    MvPolynomial.eval x (alternantMatrix p).det =
      (Matrix.of fun i j => (p i).eval (x j)).det := by
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change (MvPolynomial.eval x) ((p i).eval₂ MvPolynomial.C (MvPolynomial.X j)) = (p i).eval (x j)
  rw [Polynomial.hom_eval₂]
  have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id R := by
    apply RingHom.ext
    intro r
    simp [RingHom.comp_apply]
  rw [hc, MvPolynomial.eval_X]
  rfl

omit [IsDomain R] in
theorem eval_symbolicV (x : Fin k → R) :
    MvPolynomial.eval x (symbolicV k) = (Matrix.vandermonde x).det := by
  rw [symbolicV, RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp [Matrix.vandermonde_apply]

end Determinants
end SharpDifference



