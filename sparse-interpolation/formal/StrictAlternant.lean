import StrictRows

open scoped BigOperators
open SharpDifference Polynomial

namespace GrenetStrict

section Alternants

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] {k : ℕ}

omit [IsDomain R] [IsDomain S] in
theorem map_alternant_det (f : R →+* S) (P : Fin k → Polynomial R) :
    MvPolynomial.map f (alternantMatrix P).det =
      (alternantMatrix (fun i => (P i).map f)).det := by
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change MvPolynomial.map f ((P i).eval₂ MvPolynomial.C (MvPolynomial.X j)) =
    ((P i).map f).eval₂ MvPolynomial.C (MvPolynomial.X j)
  have hc : (MvPolynomial.map f : MvPolynomial (Fin k) R →+* MvPolynomial (Fin k) S).comp
      MvPolynomial.C = (MvPolynomial.C (σ := Fin k)).comp f := by
    apply RingHom.ext
    intro a
    exact MvPolynomial.map_C f a
  rw [Polynomial.hom_eval₂, hc, MvPolynomial.map_X, Polynomial.eval₂_map]

omit [IsDomain R] [IsDomain S] in
theorem map_symbolicV (f : R →+* S) (k : ℕ) :
    MvPolynomial.map f (symbolicV (R := R) k) = symbolicV (R := S) k := by
  rw [symbolicV_eq_prod, symbolicV_eq_prod, map_prod]
  apply Finset.prod_congr rfl
  intro ij _
  simp [gap]

omit [CommRing R] [IsDomain R] in
theorem det_descPochhammer_alternant :
    (alternantMatrix (fun i : Fin k => descPochhammer S i.val)).det =
      symbolicV (R := S) k := by
  let A := MvPolynomial (Fin k) S
  let P := fun j : Fin k => descPochhammer A j.val
  have he : (alternantMatrix (fun i : Fin k => descPochhammer S i.val)).transpose =
      Matrix.of (fun i j => (P j).eval (MvPolynomial.X i)) := by
    apply Matrix.ext
    intro i j
    change (descPochhammer S j.val).eval₂ MvPolynomial.C (MvPolynomial.X i) =
      (descPochhammer A j.val).eval (MvPolynomial.X i)
    have hm : (descPochhammer S j.val).map (MvPolynomial.C : S →+* A) =
        descPochhammer A j.val := descPochhammer_map _ _
    rw [← hm, Polynomial.eval_map]
  rw [← Matrix.det_transpose (alternantMatrix (fun i : Fin k => descPochhammer S i.val)), he]
  exact (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde _ P
    (fun i => descPochhammer_natDegree A i.val) (fun i => monic_descPochhammer A i.val)).symm

/-- Divide symbolically, then reduce. This works when numeric exponent
differences vanish in the residue field. -/
theorem symbolic_unit_of_desc_reduction (f : R →+* S) (P : Fin k → Polynomial R)
    (hP : ∀ i, (P i).map f = descPochhammer S i.val) :
    ∃ Q : MvPolynomial (Fin k) R, (alternantMatrix P).det = symbolicV k * Q ∧
      MvPolynomial.map f Q = 1 := by
  obtain ⟨Q, hQ⟩ := symbolicV_dvd_alternant P
  refine ⟨Q, hQ, ?_⟩
  have hh := congrArg (MvPolynomial.map f) hQ
  rw [map_alternant_det, map_mul, map_symbolicV] at hh
  simp_rw [hP] at hh
  rw [det_descPochhammer_alternant] at hh
  have hn : symbolicV (R := S) k ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr MvPolynomial.X_injective
  apply mul_left_cancel₀ hn
  simpa only [mul_one] using hh.symm

end Alternants

variable (p : ℕ) [Fact p.Prime]

theorem strict_symbolic_quotient (c : ℚ) (hc : StrictStep p c) (k M : ℕ)
    (hM : ∀ i : Fin k, i.val ≤ M) :
    ∃ Q : MvPolynomial (Fin k) (D p),
      (alternantMatrix (fun i : Fin k => rowPoly p c hc M i.val)).det = symbolicV k * Q ∧
      MvPolynomial.map (residue p) Q = 1 :=
  symbolic_unit_of_desc_reduction (residue p) _ (fun i => rowPoly_reduce p c hc M i.val (hM i))

end GrenetStrict

