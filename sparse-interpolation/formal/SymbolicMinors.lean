import SparseEvaluation
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

open Matrix Polynomial

namespace Round4Transfer

open GrenetMcCoy

variable {R S ι κ F K : Type*}

section Map

variable [CommRing R] [CommRing S] [Fintype κ] [DecidableEq κ]

theorem map_fullMinor (f : R →+* S) (A : Matrix ι κ R) (rows : κ → ι) :
    f (A.submatrix rows id).det = ((A.map f).submatrix rows id).det :=
  f.map_det _

/-- The ideal of full-column minors commutes with base change. -/
theorem map_fullMinorIdeal (f : R →+* S) (A : Matrix ι κ R) :
    Ideal.map f (fullMinorIdeal A) = fullMinorIdeal (A.map f) := by
  rw [fullMinorIdeal, Ideal.map_span, fullMinorIdeal]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨rows, rfl⟩, rfl⟩
    exact ⟨rows, (map_fullMinor f A rows).symm⟩
  · rintro ⟨rows, rfl⟩
    exact ⟨_, ⟨rows, rfl⟩, map_fullMinor f A rows⟩

theorem injective_of_fullMinorIdeal_eq_top (A : Matrix ι κ R)
    (hA : fullMinorIdeal A = ⊤) : Function.Injective A.mulVec := by
  apply (mulVec_injective_iff_full_minor_annihilator A).mpr
  intro r hr
  have hann := (mem_fullMinorIdeal_annihilator A r).mpr hr
  have h1 : (1 : R) ∈ fullMinorIdeal A := by simp [hA]
  simpa using Submodule.mem_annihilator.mp hann 1 h1

end Map

section Roots

variable [Field F] [Field K] [IsAlgClosed K]

/-- In one variable, no common zero in an algebraically closed extension
is equivalent to the generators spanning the unit ideal. -/
theorem polynomial_span_eq_top_iff_no_common_root (f : F →+* K) (P : Set F[X]) :
    Ideal.span P = ⊤ ↔ ∀ z : K, ∃ p ∈ P, p.eval₂ f z ≠ 0 := by
  classical
  constructor
  · intro h z
    by_contra! hz
    let ev := eval₂RingHom f z
    have ht : Ideal.map ev (Ideal.span P) = ⊥ := by
      rw [Ideal.map_span, Ideal.span_eq_bot]
      rintro _ ⟨p, hp, rfl⟩
      exact hz p hp
    rw [h, Ideal.map_top] at ht
    exact top_ne_bot ht
  · intro h
    by_contra hn
    let g := Submodule.IsPrincipal.generator (Ideal.span P)
    have hg : Ideal.span ({g} : Set F[X]) = Ideal.span P :=
      Ideal.span_singleton_generator _
    have hd : g.degree ≠ 0 := by
      intro hd
      apply hn
      rw [← hg, Ideal.span_singleton_eq_top]
      exact Polynomial.isUnit_iff_degree_eq_zero.mpr hd
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_eval₂_eq_zero f g hd
    obtain ⟨p, hp, hnz⟩ := h z
    have hm : p ∈ Ideal.span ({g} : Set F[X]) := hg ▸ Ideal.subset_span hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hm
    exact hnz (by rw [eval₂_mul, hz, zero_mul])

end Roots

/-- The evaluation matrix at the symbolic nodes Z + offset(i). -/
noncomputable def symbolicMatrix (offset : ι → ℕ) (E : Finset ℕ) :
    Matrix ι E ℚ[X] :=
  evaluationMatrix (fun i => X + C (offset i : ℚ)) E

theorem symbolicMatrix_specialize [CommRing S] (offset : ι → ℕ) (E : Finset ℕ)
    (f : ℚ →+* S) (z : S) :
    (symbolicMatrix offset E).map (eval₂RingHom f z) =
      evaluationMatrix (fun i => z + (offset i : S)) E := by
  ext i e
  change (eval₂RingHom f z) ((X + C (offset i : ℚ)) ^ e.val) =
    (z + (offset i : S)) ^ e.val
  rw [map_pow, map_add]
  change (eval₂ f z X + eval₂ f z (C (offset i : ℚ))) ^ e.val = _
  rw [eval₂_X, eval₂_C, map_natCast]

/-- A symbolic unit-ideal certificate guarantees injectivity in any
specialization to a commutative rational algebra. -/
theorem normalized_injective [CommRing S] (offset : ι → ℕ) (E : Finset ℕ)
    (f : ℚ →+* S) (z : S) (hE : fullMinorIdeal (symbolicMatrix offset E) = ⊤) :
    Function.Injective (evaluationMatrix (fun i => z + (offset i : S)) E).mulVec := by
  apply injective_of_fullMinorIdeal_eq_top
  rw [← symbolicMatrix_specialize offset E f z, ← map_fullMinorIdeal, hE, Ideal.map_top]

/-- In an algebraically closed extension of Q, absence of a common zero
for the specialized full minors yields the symbolic unit ideal. -/
theorem symbolic_fullMinorIdeal_eq_top_of_no_common_root [Field K] [IsAlgClosed K]
    (offset : ι → ℕ) (E : Finset ℕ) (f : ℚ →+* K)
    (h : ∀ z : K, ∃ rows : E → ι,
      ((evaluationMatrix (fun i => z + (offset i : K)) E).submatrix rows id).det ≠ 0) :
    fullMinorIdeal (symbolicMatrix offset E) = ⊤ := by
  unfold fullMinorIdeal
  apply (polynomial_span_eq_top_iff_no_common_root f _).mpr
  intro z
  obtain ⟨rows, hr⟩ := h z
  refine ⟨_, ⟨rows, rfl⟩, ?_⟩
  change (eval₂RingHom f z) ((symbolicMatrix offset E).submatrix rows id).det ≠ 0
  rw [map_fullMinor, symbolicMatrix_specialize]
  exact hr

/-- The rank formulation of the required algebraically closed field input. -/
theorem symbolic_fullMinorIdeal_eq_top_of_pointwise_injective [Field K] [IsAlgClosed K]
    (offset : ι → ℕ) (E : Finset ℕ) (f : ℚ →+* K)
    (h : ∀ z : K, Function.Injective (evaluationMatrix (fun i => z + (offset i : K)) E).mulVec) :
    fullMinorIdeal (symbolicMatrix offset E) = ⊤ := by
  apply symbolic_fullMinorIdeal_eq_top_of_no_common_root offset E f
  intro z
  by_contra! hr
  exact one_ne_zero ((mulVec_injective_iff_full_minor_annihilator _).mp (h z) 1
    (fun rows => by simp [hr rows]))

end Round4Transfer
