import SolverProbes
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Rat.Lemmas

noncomputable section
namespace RootSeparation.Solver

open Polynomial

def oddIntegers : Submonoid ℤ where
  carrier := {a | Odd a}
  one_mem' := odd_one
  mul_mem' := Odd.mul

abbrev OddScalars := Localization oddIntegers

theorem odd_mem {a : ℤ} : a ∈ oddIntegers ↔ Odd a := Iff.rfl

theorem odd_unit_word (p : ℕ) (a : oddIntegers) :
    IsUnit (integerToWord p a.val) := by
  have ha : Odd a.val := a.property
  have hnat : Odd a.val.natAbs := by simpa using ha
  have hc := Nat.Prime.coprime_pow_of_not_dvd (m := p) Nat.prime_two
    (show ¬ 2 ∣ a.val.natAbs by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])
  have hu := (ZMod.isUnit_iff_coprime a.val.natAbs (2^p)).2 hc
  change IsUnit (a.val : ZMod (2^p))
  cases hi : a.val <;> simp [hi] at hu ⊢
  · exact hu
  · simpa only [neg_add_rev] using hu.neg

def localizedWord (p : ℕ) : OddScalars →+* ZMod (2^p) :=
  IsLocalization.lift (odd_unit_word p)

theorem odd_unit_rat (a : oddIntegers) : IsUnit (Int.castRingHom ℚ a.val) :=
  isUnit_iff_ne_zero.2 (Int.cast_ne_zero.2 (by
    intro h
    have ha : Odd a.val := a.property
    simp [h] at ha))

def localizedRat : OddScalars →+* ℚ := IsLocalization.lift odd_unit_rat

instance : Nontrivial OddScalars :=
  ⟨⟨0,1,fun h => zero_ne_one (show (0 : ℚ) = 1 by
    simpa only [map_zero,map_one] using congrArg localizedRat h)⟩⟩

theorem localizedRat_injective : Function.Injective localizedRat := by
  rw [localizedRat]
  apply (IsLocalization.lift_injective_iff _).2
  intro x y
  constructor
  · intro h
    have hh := congrArg localizedRat h
    simpa only [localizedRat, IsLocalization.lift_eq] using hh
  · intro h
    exact congrArg (algebraMap ℤ OddScalars) (Int.cast_injective h)

theorem localizedRat_range (q : ℚ) : q ∈ localizedRat.range ↔ Odd q.den := by
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨⟨n,d⟩,he⟩ := IsLocalization.surj oddIntegers x
    have hd : Odd d.val := d.property
    have eq : localizedRat x * (d.val : ℚ) = (n : ℚ) := by
      have h := congrArg localizedRat he
      simpa only [map_mul, localizedRat, IsLocalization.lift_eq, Int.castRingHom] using h
    have hnz : (d.val : ℚ) ≠ 0 := Int.cast_ne_zero.2 (by
      intro h
      simp [h] at hd)
    have hq := (eq_div_iff hnz).2 eq
    have hdiv : ((localizedRat x).den : ℤ) ∣ d.val := by
      rw [hq, ← Rat.divInt_eq_div]
      exact Rat.den_dvd n d.val
    exact hd.natAbs.of_dvd_nat (by simpa using Int.natAbs_dvd_natAbs.mpr hdiv)
  · intro h
    let d : oddIntegers := ⟨q.den, (Int.natAbs_odd (n := (q.den : ℤ))).1
      (by simpa only [Int.natAbs_natCast] using h)⟩
    refine ⟨IsLocalization.mk' OddScalars q.num d,?_⟩
    apply (IsLocalization.lift_mk'_spec (S := OddScalars) (M := oddIntegers)
      (g := Int.castRingHom ℚ) odd_unit_rat q.num q d).2
    change (q.num : ℚ) = (↑(q.den : ℤ) : ℚ) * q
    rw [Int.cast_natCast, Rat.den_mul_eq_num]

def localizedPolynomial (f : ℤ[X]) : OddScalars[X] :=
  f.map (algebraMap ℤ OddScalars)

abbrev IntegralRing (f : ℤ[X]) := AdjoinRoot (localizedPolynomial f)
abbrev RationalRing (f : ℤ[X]) := AdjoinRoot (f.map (Int.castRingHom ℚ))

/-- The printed p-word quotient of the odd-localized coefficient ring. -/
def integralWord (f : ℤ[X]) (p : ℕ) : IntegralRing f →+* WordRing f p :=
  AdjoinRoot.lift ((AdjoinRoot.of (f.map (integerToWord p))).comp (localizedWord p))
    (AdjoinRoot.root (f.map (integerToWord p))) (by
      rw [← eval₂_map, localizedPolynomial, Polynomial.map_map]
      have he : (localizedWord p).comp (algebraMap ℤ OddScalars) = integerToWord p :=
        Subsingleton.elim _ _
      rw [he]
      exact AdjoinRoot.eval₂_root _)

def integerIntegral (f : ℤ[X]) : IntegerRing f →+* IntegralRing f :=
  changeRoot f (algebraMap ℤ OddScalars)

theorem integralWord_integerIntegral (f : ℤ[X]) (p : ℕ) (x : IntegerRing f) :
    integralWord f p (integerIntegral f x) = fromInteger f p x := by
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    have hg := congrArg (integralWord f p) (changeRoot_mk f (algebraMap ℤ OddScalars) g)
    change integralWord f p (integerIntegral f (AdjoinRoot.mk f g)) =
      integralWord f p (AdjoinRoot.mk (localizedPolynomial f) (g.map (algebraMap ℤ OddScalars))) at hg
    refine hg.trans ?_
    unfold integralWord fromInteger
    rw [changeRoot_mk, AdjoinRoot.lift_mk, ← eval₂_map, Polynomial.map_map]
    have he : (localizedWord p).comp (algebraMap ℤ OddScalars) = integerToWord p :=
      Subsingleton.elim _ _
    rw [he]
    exact AdjoinRoot.aeval_eq _

theorem integralWord_surjective {f : ℤ[X]} (hf : f.Monic) (p : ℕ) (hp : 0 < p) :
    Function.Surjective (integralWord f p) := by
  intro x
  obtain ⟨y,hy⟩ := fromInteger_surjective hf p hp x
  exact ⟨integerIntegral f y, (integralWord_integerIntegral f p y).trans hy⟩

def integerRational (f : ℤ[X]) : IntegerRing f →+* RationalRing f :=
  changeRoot f (Int.castRingHom ℚ)

def integralRational (f : ℤ[X]) : IntegralRing f →+* RationalRing f :=
  AdjoinRoot.lift ((AdjoinRoot.of (f.map (Int.castRingHom ℚ))).comp localizedRat)
    (AdjoinRoot.root (f.map (Int.castRingHom ℚ))) (by
      rw [← eval₂_map, localizedPolynomial, Polynomial.map_map]
      have he : localizedRat.comp (algebraMap ℤ OddScalars) = Int.castRingHom ℚ :=
        Subsingleton.elim _ _
      rw [he]
      exact AdjoinRoot.eval₂_root _)

theorem integralRational_mk (f : ℤ[X]) (g : OddScalars[X]) :
    integralRational f (AdjoinRoot.mk (localizedPolynomial f) g) =
      AdjoinRoot.mk (f.map (Int.castRingHom ℚ)) (g.map localizedRat) := by
  rw [integralRational, AdjoinRoot.lift_mk, ← eval₂_map]
  exact AdjoinRoot.aeval_eq _

theorem integralRational_integerIntegral (f : ℤ[X]) (x : IntegerRing f) :
    integralRational f (integerIntegral f x) = integerRational f x := by
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    have hg := congrArg (integralRational f) (changeRoot_mk f (algebraMap ℤ OddScalars) g)
    change integralRational f (integerIntegral f (AdjoinRoot.mk f g)) =
      integralRational f (AdjoinRoot.mk (localizedPolynomial f) (g.map (algebraMap ℤ OddScalars))) at hg
    refine hg.trans ?_
    rw [integerRational, changeRoot_mk, integralRational_mk, Polynomial.map_map]
    have he : localizedRat.comp (algebraMap ℤ OddScalars) = Int.castRingHom ℚ := Subsingleton.elim _ _
    rw [he]

section IntegralCoordinates

variable {f : ℤ[X]} {e : ℕ}

def integralCoords (hf : f.Monic) (he : f.natDegree = e) : IntegralRing f ≃+ (Fin e → OddScalars) :=
  coordinate (localizedPolynomial f) (hf.map _) ((hf.natDegree_map _).trans he)

def rationalCoords (hf : f.Monic) (he : f.natDegree = e) : RationalRing f ≃+ (Fin e → ℚ) :=
  coordinate (f.map (Int.castRingHom ℚ)) (hf.map _) ((hf.natDegree_map _).trans he)

theorem integralRational_coordinate (hf : f.Monic) (he : f.natDegree = e)
    (x : IntegralRing f) (i : Fin e) :
    rationalCoords hf he (integralRational f x) i = localizedRat (integralCoords hf he x i) := by
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    rw [integralRational_mk, rationalCoords, integralCoords, coordinate_mk, coordinate_mk]
    have hm : (localizedPolynomial f).map localizedRat = f.map (Int.castRingHom ℚ) := by
      rw [localizedPolynomial, Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    have hmon : (localizedPolynomial f).Monic := hf.map (algebraMap ℤ OddScalars)
    rw [← hm, ← map_modByMonic localizedRat hmon, coeff_map]

theorem integralRational_injective (hf : f.Monic) : Function.Injective (integralRational f) := by
  intro x y hxy
  apply (integralCoords hf rfl).injective
  funext i
  apply localizedRat_injective
  rw [← integralRational_coordinate hf rfl x i, ← integralRational_coordinate hf rfl y i, hxy]

theorem integralRational_range (hf : f.Monic) (he : f.natDegree = e) (x : RationalRing f) :
    x ∈ (integralRational f).range ↔ ∀ i, Odd (rationalCoords hf he x i).den := by
  constructor
  · rintro ⟨y,rfl⟩ i
    rw [integralRational_coordinate hf he]
    exact (localizedRat_range _).1 ⟨_,rfl⟩
  · intro h
    choose z hz using fun i => (localizedRat_range (rationalCoords hf he x i)).2 (h i)
    refine ⟨(integralCoords hf he).symm z,?_⟩
    apply (rationalCoords hf he).injective
    funext i
    rw [integralRational_coordinate hf he]
    have hi := congrFun ((integralCoords hf he).apply_symm_apply z) i
    rw [hi]
    exact hz i

/-- Regard exact rational output as a p-word only when all denominators
    are odd. The conversion is the unique preimage in the verified
    integral subring, followed by its residue map. -/
def tryWord (_hf : f.Monic) (p : ℕ) (x : RationalRing f) : Option (WordRing f p) := by
  classical
  exact if h : x ∈ (integralRational f).range then
    some (integralWord f p (Classical.choose h)) else none

theorem tryWord_integral (hf : f.Monic) (p : ℕ) (x : IntegralRing f) :
    tryWord hf p (integralRational f x) = some (integralWord f p x) := by
  classical
  have hx : integralRational f x ∈ (integralRational f).range := ⟨x,rfl⟩
  unfold tryWord
  rw [dif_pos hx]
  congr 2
  exact integralRational_injective hf (Classical.choose_spec hx)

theorem tryWord_integer (hf : f.Monic) (p : ℕ) (x : IntegerRing f) :
    tryWord hf p (integerRational f x) = some (fromInteger f p x) := by
  rw [← integralRational_integerIntegral, tryWord_integral, integralWord_integerIntegral]

theorem word_two_pow (f : ℤ[X]) (p : ℕ) : (2 : WordRing f p)^p = 0 := by
  have h : (2 : ZMod (2^p))^p = 0 := by
    change ((↑(2 : ℕ) : ZMod (2^p))^p) = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  simpa using congrArg (AdjoinRoot.of (f.map (integerToWord p))) h

theorem tryWord_error (hf : f.Monic) (p : ℕ) (x : IntegerRing f) (error : IntegralRing f) :
    tryWord hf p ((integerRational f x) + (2 : RationalRing f)^p * integralRational f error) =
      some (fromInteger f p x) := by
  have hx : integerRational f x + 2^p * integralRational f error =
      integralRational f (integerIntegral f x + 2^p * error) := by
    rw [map_add,map_mul,map_pow,map_ofNat,integralRational_integerIntegral]
  rw [hx,tryWord_integral,map_add,map_mul,map_pow,map_ofNat,
    integralWord_integerIntegral, word_two_pow,zero_mul,add_zero]

end IntegralCoordinates

#print axioms integralRational_integerIntegral
#print axioms integralRational_injective
#print axioms integralRational_range
#print axioms tryWord_integral
#print axioms tryWord_error
#print axioms localizedRat_injective
#print axioms localizedRat_range
#print axioms integralWord_integerIntegral
#print axioms integralWord_surjective

end RootSeparation.Solver
