
import RootExecution
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma

noncomputable section
namespace RootSeparation.Solver

open Polynomial
open scoped BigOperators

section ChangeCoefficients

variable {R S : Type*} [CommRing R] [CommRing S]
variable (f : R[X]) (φ : R →+* S)

def changeRoot : AdjoinRoot f →+* AdjoinRoot (f.map φ) :=
  AdjoinRoot.lift ((AdjoinRoot.of (f.map φ)).comp φ) (AdjoinRoot.root (f.map φ))
    (by rw [← eval₂_map]; exact AdjoinRoot.eval₂_root _)

theorem changeRoot_mk (g : R[X]) :
    changeRoot f φ (AdjoinRoot.mk f g) = AdjoinRoot.mk (f.map φ) (g.map φ) := by
  rw [changeRoot, AdjoinRoot.lift_mk, ← eval₂_map]
  exact AdjoinRoot.aeval_eq _

theorem changeRoot_of (x : R) :
    changeRoot f φ (AdjoinRoot.of f x) = AdjoinRoot.of (f.map φ) (φ x) := by
  unfold changeRoot
  exact AdjoinRoot.lift_of _

/-- Kept at the declared source degree even under reduction. -/
def coordinate {e : ℕ} (hf : f.Monic) (hd : f.natDegree = e) :
    AdjoinRoot f ≃+ (Fin e → R) :=
  (AdjoinRoot.powerBasisAux' hf).equivFun.toAddEquiv.trans
    { toFun := fun x i => x (Fin.cast hd.symm i)
      invFun := fun x i => x (Fin.cast hd i)
      left_inv := fun x => funext fun i => by simp
      right_inv := fun x => funext fun i => by simp
      map_add' := fun _ _ => rfl }

theorem coordinate_mk {e : ℕ} (hf : f.Monic) (hd : f.natDegree = e)
    (g : R[X]) (i : Fin e) :
    coordinate f hf hd (AdjoinRoot.mk f g) i = (g %ₘ f).coeff i.val := by
  subst e
  rfl

theorem changeRoot_coordinate [Nontrivial S] {e : ℕ} (hf : f.Monic) (hd : f.natDegree = e)
    (x : AdjoinRoot f) (i : Fin e) :
    coordinate (f.map φ) (hf.map φ) ((hf.natDegree_map φ).trans hd) (changeRoot f φ x) i =
      φ (coordinate f hf hd x i) := by
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    rw [changeRoot_mk, coordinate_mk, coordinate_mk, ← map_modByMonic φ hf, coeff_map]

end ChangeCoefficients

def integerToWord (p : ℕ) : ℤ →+* ZMod (2^p) := Int.castRingHom _
abbrev WordRing (f : ℤ[X]) (p : ℕ) := AdjoinRoot (f.map (integerToWord p))
abbrev IntegerRing (f : ℤ[X]) := AdjoinRoot f

def wordCoords {f : ℤ[X]} {e : ℕ} (hf : f.Monic) (he : f.natDegree = e) (p : ℕ) (hp : 0 < p) :
    WordRing f p ≃+ RootSeparation.Execution.Coords (Fin e) p := by
  haveI : Fact (1 < 2^p) := ⟨Nat.one_lt_two_pow hp.ne'⟩
  exact coordinate (f.map (integerToWord p)) (hf.map _) ((hf.natDegree_map _).trans he)

def fromInteger (f : ℤ[X]) (p : ℕ) : IntegerRing f →+* WordRing f p :=
  changeRoot f (integerToWord p)

/-- Immutable creation-time section. It stores the least nonnegative
    integer representative of every old coefficient. It is not used as
    an arithmetic homomorphism. -/
def liftCanonical {f : ℤ[X]} {e p : ℕ} (hf : f.Monic) (he : f.natDegree = e)
    (hp : 0 < p) (x : WordRing f p) : IntegerRing f :=
  (coordinate f hf he).symm fun i => ((wordCoords hf he p hp x i).val : ℤ)

theorem liftCanonical_coordinate {f : ℤ[X]} {e p : ℕ} (hf : f.Monic) (he : f.natDegree = e)
    (hp : 0 < p) (x : WordRing f p) (i : Fin e) :
    coordinate f hf he (liftCanonical hf he hp x) i = ((wordCoords hf he p hp x i).val : ℤ) := by
  exact congrFun ((coordinate f hf he).apply_symm_apply _) i

theorem liftCanonical_section {f : ℤ[X]} {e p : ℕ} (hf : f.Monic) (he : f.natDegree = e)
    (hp : 0 < p) (x : WordRing f p) :
    fromInteger f p (liftCanonical hf he hp x) = x := by
  haveI : Fact (1 < 2^p) := ⟨Nat.one_lt_two_pow hp.ne'⟩
  haveI : NeZero (2^p) := ⟨by positivity⟩
  apply (wordCoords hf he p hp).injective
  funext i
  change (coordinate (f.map (integerToWord p)) (hf.map _) _
    (changeRoot f (integerToWord p) (liftCanonical hf he hp x))) i = _
  rw [changeRoot_coordinate, liftCanonical_coordinate]
  change ((↑(wordCoords hf he p hp x i).val : ℤ) : ZMod (2^p)) = _
  rw [Int.cast_natCast]
  exact (ZMod.natCast_val _).trans (ZMod.cast_id _ _)

theorem fromInteger_surjective {f : ℤ[X]} (hf : f.Monic) (p : ℕ) (hp : 0 < p) :
    Function.Surjective (fromInteger f p) :=
  fun x => ⟨liftCanonical hf rfl hp x, liftCanonical_section hf rfl hp x⟩

theorem liftCanonical_preserved {f : ℤ[X]} {e p q : ℕ}
    (hf : f.Monic) (he : f.natDegree = e) (hp : 0 < p) (hq : 0 < q) (h : p ≤ q)
    (x : WordRing f p) :
    liftCanonical hf he hq (fromInteger f q (liftCanonical hf he hp x)) =
      liftCanonical hf he hp x := by
  haveI : Fact (1 < 2^q) := ⟨Nat.one_lt_two_pow hq.ne'⟩
  haveI : NeZero (2^p) := ⟨by positivity⟩
  apply (coordinate f hf he).injective
  funext i
  rw [liftCanonical_coordinate]
  have hc := changeRoot_coordinate f (integerToWord q) hf he (liftCanonical hf he hp x) i
  change wordCoords hf he q hq (fromInteger f q (liftCanonical hf he hp x)) i =
    integerToWord q (coordinate f hf he (liftCanonical hf he hp x) i) at hc
  rw [hc,liftCanonical_coordinate]
  congr 1
  change (((↑(wordCoords hf he p hp x i).val : ℤ) : ZMod (2^q))).val = _
  rw [Int.cast_natCast]
  exact ZMod.val_natCast_of_lt ((ZMod.val_lt _).trans_le (Nat.pow_le_pow_right (by decide) h))

/-- The field of rational coefficients used by the source. Reduction
    modulo two of f supplies irreducibility over Q by Gauss's lemma. -/
theorem rational_irreducible {f : ℤ[X]} (hf : f.Monic)
    (hred : Irreducible (f.map (Int.castRingHom (ZMod 2)))) :
    Irreducible (f.map (Int.castRingHom ℚ)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hf.isPrimitive).1
  refine ⟨?_, ?_⟩
  · exact fun hu => hred.not_isUnit (hu.map (Polynomial.mapRingHom (Int.castRingHom (ZMod 2))))
  · intro a b hab
    have hmaps : f.map (Int.castRingHom (ZMod 2)) =
        a.map (Int.castRingHom (ZMod 2)) * b.map (Int.castRingHom (ZMod 2)) := by rw [hab, Polynomial.map_mul]
    have hunit := hred.isUnit_or_isUnit hmaps
    have hleads : a.leadingCoeff * b.leadingCoeff = 1 := by rw [← leadingCoeff_mul, ← hab, hf]
    have liftUnit (g : ℤ[X]) (hg : IsUnit g.leadingCoeff)
        (h : IsUnit (g.map (Int.castRingHom (ZMod 2)))) : IsUnit g := by
      exact isUnit_of_isUnit_leadingCoeff_of_isUnit_map (Int.castRingHom (ZMod 2)) hg h
    rcases hunit with h | h
    · exact Or.inl (liftUnit a (isUnit_of_mul_isUnit_left (hleads ▸ isUnit_one)) h)
    · exact Or.inr (liftUnit b (isUnit_of_mul_isUnit_right (hleads ▸ isUnit_one)) h)

#print axioms changeRoot_coordinate
#print axioms liftCanonical_section
#print axioms liftCanonical_preserved
#print axioms rational_irreducible

end RootSeparation.Solver

