import AOracleThreshold
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# Additive coordinates for the A1 double quotient

The coefficient representation of
(Z/(2^p))[U]/(f)[V]/(V^ell) is verified directly by monic remainders.
Oracle counts are made for each original basis coordinate. Irreducibility
is not needed for additive reconstruction; when the source uses an
irreducible residue polynomial the same quotient fits the statement.
-/

open scoped BigOperators Polynomial

namespace AOracleCoordinates

open Polynomial AOracleThreshold

section Monic
variable {R : Type*} [CommRing R]

/-- The n-th coefficient of the unique monic remainder. -/
noncomputable def coord (f : R[X]) (hf : f.Monic) (n : ℕ) : AdjoinRoot f →+ R :=
  ((Polynomial.lcoeff R n).comp (AdjoinRoot.modByMonicHom hf)).toAddMonoidHom

@[simp] theorem coord_apply (f : R[X]) (hf : f.Monic) (n : ℕ) (x : AdjoinRoot f) :
    coord f hf n x = (AdjoinRoot.modByMonicHom hf x).coeff n := rfl

theorem rem_natDegree_lt (f : R[X]) (hf : f.Monic) (hd : 0 < f.natDegree) (x : AdjoinRoot f) :
    (AdjoinRoot.modByMonicHom hf x).natDegree < f.natDegree := by
  induction x using AdjoinRoot.induction_on with
  | _ p =>
    rw [AdjoinRoot.modByMonicHom_mk]
    apply Polynomial.natDegree_modByMonic_lt p hf
    intro h
    simp [h] at hd

/-- A degree-e monic quotient is determined by its e real coefficient words. -/
theorem coord_injective (f : R[X]) (hf : f.Monic) (hd : 0 < f.natDegree) :
    Function.Injective (fun x : AdjoinRoot f => fun j : Fin f.natDegree => coord f hf j.val x) := by
  intro x y h
  apply (AdjoinRoot.mk_leftInverse hf).injective
  apply Polynomial.ext
  intro j
  by_cases hj : j < f.natDegree
  · exact congrFun h ⟨j,hj⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((rem_natDegree_lt f hf hd x).trans_le (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt ((rem_natDegree_lt f hf hd y).trans_le (by omega))]

end Monic

section Double

abbrev Base (p : ℕ) := ZMod (2^p)

abbrev Truncated {p : ℕ} (f : (Base p)[X]) (ell : ℕ) :=
  AdjoinRoot ((X : (AdjoinRoot f)[X])^ell)

/-- One coordinate of the actual two formal coordinates U,V; it is
only an additive map, not claimed a ring homomorphism. -/
noncomputable def doubleCoord {p : ℕ} (f : (Base p)[X]) (hf : f.Monic) (ell : ℕ)
    (ij : Fin f.natDegree × Fin ell) :
    Truncated f ell →+ Base p :=
  (coord f hf ij.1.val).comp
    (coord ((X : (AdjoinRoot f)[X])^ell) (monic_X_pow ell) ij.2.val)

theorem coord_indices (e ell : ℕ) :
    Fintype.card (Fin e × Fin ell) = e*ell := by simp

theorem doubleCoord_injective {p : ℕ} (hp : 0 < p) (f : (Base p)[X]) (hf : f.Monic)
    (he : 0 < f.natDegree) (ell : ℕ) (hell : 0 < ell) :
    Function.Injective (fun x : Truncated f ell => fun ij : Fin f.natDegree × Fin ell =>
      doubleCoord f hf ell ij x) := by
  let g := (X : (AdjoinRoot f)[X])^ell
  letI : Fact (1 < (2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) (by omega)⟩
  haveI : Nontrivial (AdjoinRoot f) := nontrivial_of_ne _ _
    (show (1 : AdjoinRoot f) ≠ 0 by
      have h := AdjoinRoot.mk_ne_zero_of_natDegree_lt hf
        (show (1 : (Base p)[X]) ≠ 0 from one_ne_zero) (by simpa using he)
      simp only [map_one] at h
      exact h)
  have hg : g.natDegree = ell := by simp [g]
  intro x y h
  apply coord_injective g (monic_X_pow ell) (hg.symm ▸ hell)
  funext j
  apply coord_injective f hf he
  funext i
  have hj : j.val < ell := by simpa only [hg] using j.isLt
  exact congrFun h (i,⟨j.val,hj⟩)

/-- Exact abstract finite oracle reduction for a double-truncated register:
e*ell calls determine its unique value, including signed witnesses. -/
theorem reconstruct_from_counters {D W : Type*} [Fintype D] [Fintype W]
    {p : ℕ} (hp : 0 < p) (f : (Base p)[X]) (hf : f.Monic) (he : 0 < f.natDegree)
    (ell : ℕ) (hell : 0 < ell)
    (parse : D → Option W) (encode : W ↪ D)
    (exactly : ∀ d w, parse d = some w ↔ d = encode w)
    (valid : W → Bool) (weight : W → Truncated f ell) :
    ∃! z : Truncated f ell, ∀ ij,
      doubleCoord f hf ell ij z =
        (countQuery parse valid (fun w => doubleCoord f hf ell ij (weight w)) : Base p) := by
  refine ⟨∑ w, if valid w then weight w else 0, ?_, ?_⟩
  · intro ij
    exact (countQuery_coordinate parse encode exactly valid weight (doubleCoord f hf ell) ij).symm
  · intro z hz
    apply doubleCoord_injective hp f hf he ell hell
    funext ij
    exact (hz ij).trans (countQuery_coordinate parse encode exactly valid weight
      (doubleCoord f hf ell) ij)

end Double

#print axioms rem_natDegree_lt
#print axioms coord_injective
#print axioms coord_indices
#print axioms doubleCoord_injective
#print axioms reconstruct_from_counters

end AOracleCoordinates

