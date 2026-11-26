import SolverOddLocalization
import SolverScalarValuation

noncomputable section
namespace RootSeparation.Solver
open Polynomial
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem scalarOrder_int_threshold (n : ℕ) (x : ℤ) :
    (↑(n : ℤ) : WithTop ℤ) ≤ scalarOrder (x:ℚ) ↔ (2:ℤ)^n ∣ x := by
  rw [show (2:ℤ) = ((2:ℕ):ℤ) from rfl, padicValInt_dvd_iff]
  by_cases hx : x = 0
  · simp [hx,scalarOrder]
  rw [scalarOrder,if_neg (Int.cast_ne_zero.2 hx),padicValRat.of_int,WithTop.coe_le_coe]
  simp [hx]

theorem scalarOrder_odd (x : ℤ) (hx : Odd x) : scalarOrder (x:ℚ) = 0 := by
  have hz : x ≠ 0 := fun h => by simp [h] at hx
  rw [scalarOrder,if_neg (Int.cast_ne_zero.2 hz),padicValRat.of_int]
  have hnd : ¬ (2 : ℤ) ∣ x := by
    rwa [← even_iff_two_dvd, Int.not_even_iff_odd]
  rw [padicValInt.eq_zero_of_not_dvd hnd,Nat.cast_zero,WithTop.coe_zero]

theorem localizedWord_zero_iff (p : ℕ) (x : OddScalars) :
    localizedWord p x = 0 ↔ (↑(p:ℤ) : WithTop ℤ) ≤ scalarOrder (localizedRat x) := by
  obtain ⟨⟨n,d⟩,h⟩ := IsLocalization.surj oddIntegers x
  have hQ : localizedRat x * (d.val:ℚ) = (n:ℚ) := by
    simpa only [map_mul,localizedRat,IsLocalization.lift_eq] using congrArg localizedRat h
  have hW : localizedWord p x * integerToWord p d.val = integerToWord p n := by
    simpa only [map_mul,localizedWord,IsLocalization.lift_eq] using congrArg (localizedWord p) h
  have hV := congrArg scalarOrder hQ
  rw [scalarOrder_mul,scalarOrder_odd d.val d.property,add_zero] at hV
  have hZ : localizedWord p x = 0 ↔ integerToWord p n = 0 := by
    rw [← hW]
    simpa only [zero_mul] using ((odd_unit_word p d).mul_left_inj
      (b := localizedWord p x) (c := 0)).symm
  rw [hZ,hV,scalarOrder_int_threshold]
  change ((n : ZMod (2^p)) = 0) ↔ (2:ℤ)^p ∣ n
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_pow]
  rfl

section Coordinates

variable {f : ℤ[X]} {e : ℕ} (hf : f.Monic) (he : f.natDegree = e)

theorem integralWord_coordinate (p : ℕ) (hp : 0 < p) (x : IntegralRing f) (i : Fin e) :
    wordCoords hf he p hp (integralWord f p x) i = localizedWord p (integralCoords hf he x i) := by
  haveI : Fact (1 < 2^p) := ⟨Nat.one_lt_two_pow hp.ne'⟩
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    have hmk : integralWord f p (AdjoinRoot.mk (localizedPolynomial f) g) =
        AdjoinRoot.mk (f.map (integerToWord p)) (g.map (localizedWord p)) := by
      rw [integralWord,AdjoinRoot.lift_mk, ← eval₂_map]
      exact AdjoinRoot.aeval_eq _
    have hm : (localizedPolynomial f).map (localizedWord p) = f.map (integerToWord p) := by
      rw [localizedPolynomial,Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    have hmon : (localizedPolynomial f).Monic := hf.map _
    rw [hmk,wordCoords,integralCoords,coordinate_mk,coordinate_mk,
      ← hm,← map_modByMonic (localizedWord p) hmon,coeff_map]

def coordinateOrder (x : RationalRing f) : WithTop ℤ :=
  Finset.univ.inf fun i : Fin e => scalarOrder (rationalCoords hf he x i)

theorem le_coordinateOrder (x : RationalRing f) (n : WithTop ℤ) :
    n ≤ coordinateOrder hf he x ↔ ∀ i, n ≤ scalarOrder (rationalCoords hf he x i) := by
  simp [coordinateOrder,Finset.le_inf_iff]

theorem coordinateOrder_nonnegative (x : RationalRing f) :
    0 ≤ coordinateOrder hf he x ↔ x ∈ (integralRational f).range := by
  rw [le_coordinateOrder,integralRational_range hf he]
  simp only [scalarOrder_nonnegative_iff]

theorem coordinateOrder_zero_iff (p : ℕ) (hp : 0 < p) (x : IntegralRing f) :
    integralWord f p x = 0 ↔ (↑(p : ℤ) : WithTop ℤ) ≤ coordinateOrder hf he (integralRational f x) := by
  rw [le_coordinateOrder]
  constructor
  · intro hx i
    rw [integralRational_coordinate hf he, ← localizedWord_zero_iff,
      ← integralWord_coordinate hf he p hp x i, hx, map_zero]
    rfl
  · intro h
    apply (wordCoords hf he p hp).injective
    funext i
    rw [map_zero, integralWord_coordinate hf he p hp x i]
    have hi := h i
    rw [integralRational_coordinate hf he, ← localizedWord_zero_iff] at hi
    exact hi

theorem canonical_probe_error (p : ℕ) (hp : 0 < p) (x : RationalRing f) (r : WordRing f p)
    (h : tryWord hf p x = some r) :
    (↑(p : ℤ) : WithTop ℤ) ≤
      coordinateOrder hf he (integerRational f (liftCanonical hf he hp r) - x) := by
  classical
  have hex : x ∈ (integralRational f).range := by
    by_contra hn
    unfold tryWord at h
    rw [dif_neg hn] at h
    cases h
  obtain ⟨y,rfl⟩ := hex
  rw [tryWord_integral,Option.some.injEq] at h
  let z := integerIntegral f (liftCanonical hf he hp r)
  have hz : integralWord f p z = r := by
    change integralWord f p (integerIntegral f (liftCanonical hf he hp r)) = r
    rw [integralWord_integerIntegral, liftCanonical_section]
  have hs : integralWord f p (z-y) = 0 := by rw [map_sub,hz,h,sub_self]
  have heq : integerRational f (liftCanonical hf he hp r) - integralRational f y =
      integralRational f (z-y) := by
    rw [map_sub]
    exact congrArg (fun a => a - integralRational f y) (integralRational_integerIntegral f _).symm
  rw [heq]
  exact (coordinateOrder_zero_iff hf he p hp (z-y)).1 hs

end Coordinates

#print axioms localizedWord_zero_iff
#print axioms integralWord_coordinate
#print axioms coordinateOrder_nonnegative
#print axioms coordinateOrder_zero_iff
#print axioms canonical_probe_error

end RootSeparation.Solver
