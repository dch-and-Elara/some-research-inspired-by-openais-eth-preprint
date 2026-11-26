import SolverCoordinates
import SolverPolynomialChoice
import RootProgram

noncomputable section
namespace RootSeparation.Solver

open Polynomial
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def reduceCoefficient (p : ℕ) (hp : 0 < p) : ZMod (2^p) →+* ZMod 2 :=
  ZMod.castHom (dvd_pow_self 2 hp.ne') (ZMod 2)

def residue {e : ℕ} (F : SourcePolynomial e) (p : ℕ) (hp : 0 < p) :
    WordRing F.f p →+* WordRing F.f 1 :=
  AdjoinRoot.lift ((AdjoinRoot.of (F.f.map (integerToWord 1))).comp (reduceCoefficient p hp))
    (AdjoinRoot.root (F.f.map (integerToWord 1))) (by
      rw [← eval₂_map, Polynomial.map_map]
      have h : (reduceCoefficient p hp).comp (integerToWord p) = integerToWord 1 :=
        Subsingleton.elim _ _
      rw [h]
      exact AdjoinRoot.eval₂_root _)

theorem residue_mk {e : ℕ} (F : SourcePolynomial e) (p : ℕ) (hp : 0 < p) (g : ℤ[X]) :
    residue F p hp (fromInteger F.f p (AdjoinRoot.mk F.f g)) =
      fromInteger F.f 1 (AdjoinRoot.mk F.f g) := by
  unfold fromInteger residue
  rw [changeRoot_mk, changeRoot_mk, AdjoinRoot.lift_mk, ← eval₂_map, Polynomial.map_map]
  have h : (reduceCoefficient p hp).comp (integerToWord p) = integerToWord 1 :=
    Subsingleton.elim _ _
  rw [h]
  exact AdjoinRoot.aeval_eq _

theorem residue_fromInteger {e : ℕ} (F : SourcePolynomial e) (p : ℕ) (hp : 0 < p)
    (x : IntegerRing F.f) :
    residue F p hp (fromInteger F.f p x) = fromInteger F.f 1 x := by
  induction x using AdjoinRoot.induction_on with
  | ih g => exact residue_mk F p hp g

private theorem integral_coordinates {e : ℕ} (F : SourcePolynomial e) (p : ℕ) (hp : 0 < p)
    (x : IntegerRing F.f) (i : Fin e) :
    wordCoords F.monic F.degree p hp (fromInteger F.f p x) i =
      integerToWord p (coordinate F.f F.monic F.degree x i) := by
  haveI : Fact (1 < 2^p) := ⟨Nat.one_lt_two_pow hp.ne'⟩
  exact changeRoot_coordinate _ _ _ _ _ _

theorem residue_surjective {e : ℕ} (F : SourcePolynomial e) (p : ℕ) (hp : 0 < p) :
    Function.Surjective (residue F p hp) := by
  intro x
  obtain ⟨y,hy⟩ := fromInteger_surjective F.monic 1 (by decide) x
  exact ⟨fromInteger F.f p y, (residue_fromInteger F p hp y).trans hy⟩

theorem residue_zero_dvd_two {e : ℕ} (F : SourcePolynomial e) (p : ℕ) (hp : 0 < p)
    (x : WordRing F.f p) (hx : residue F p hp x = 0) :
    (2 : WordRing F.f p) ∣ x := by
  let a := liftCanonical F.monic F.degree hp x
  have ha := liftCanonical_section F.monic F.degree hp x
  change fromInteger F.f p a = x at ha
  have ha0 : fromInteger F.f 1 a = 0 := by rw [← residue_fromInteger F p hp, ha, hx]
  let C := coordinate F.f F.monic F.degree
  have even (i : Fin e) : (2:ℤ) ∣ C a i := by
    have h := integral_coordinates F 1 (by decide) a i
    rw [ha0, map_zero] at h
    change 0 = ((C a i : ℤ) : ZMod 2) at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h.symm
  let b := C.symm fun i => C a i / 2
  have hab : (2 : ℕ) • b = a := by
    apply C.injective
    rw [map_nsmul]
    funext i
    change (2 : ℕ) • C b i = C a i
    have hb : C b i = C a i / 2 := congrFun (C.apply_symm_apply _) i
    rw [hb, nsmul_eq_mul]
    exact Int.mul_ediv_cancel' (even i)
  refine ⟨fromInteger F.f p b, ?_⟩
  rw [← ha, ← hab, map_nsmul, nsmul_eq_mul]
  norm_num

set_option maxHeartbeats 1000000 in
theorem unit_of_residue_ne_zero {e : ℕ} (F : SourcePolynomial e) (p : ℕ) (hp : 0 < p)
    (x : WordRing F.f p) (hx : residue F p hp x ≠ 0) : IsUnit x := by
  have hex : ∃ z : WordRing F.f 1, residue F p hp x * z = 1 := by
    let f₂ := F.f.map (Int.castRingHom (ZMod 2))
    letI : Fact (Irreducible f₂) := ⟨F.irreducibleTwo⟩
    letI : Field (AdjoinRoot f₂) := AdjoinRoot.instField (f := f₂)
    let x₂ : AdjoinRoot f₂ := residue F p hp x
    have hx₂ : x₂ ≠ 0 := hx
    let y₂ : AdjoinRoot f₂ := x₂⁻¹
    have hy₂ : x₂ * y₂ = 1 := mul_inv_cancel₀ hx₂
    exact ⟨y₂, hy₂⟩
  obtain ⟨z,hz⟩ := hex
  obtain ⟨y,hy⟩ := residue_surjective F p hp z
  have hzero : residue F p hp (1-x*y) = 0 := by
    rw [map_sub, map_one, map_mul, hy, hz, sub_self]
  obtain ⟨z,hz⟩ := residue_zero_dvd_two F p hp _ hzero
  have hpow : (2 : WordRing F.f p)^p = 0 := by
    have h : (2 : ZMod (2^p))^p = 0 := by
      change ((↑(2 : ℕ) : ZMod (2^p))^p) = 0
      rw [← Nat.cast_pow, ZMod.natCast_self]
    simpa using congrArg (AdjoinRoot.of (F.f.map (integerToWord p))) h
  have hnil : IsNilpotent (1-x*y) := ⟨p, by rw [hz, mul_pow, hpow, zero_mul]⟩
  have hunit := hnil.isUnit_one_sub
  rw [sub_sub_cancel] at hunit
  exact isUnit_of_mul_isUnit_left hunit

/-- Source binary probe in the polynomial basis, before reduction. -/
def binaryPoint {e : ℕ} (F : SourcePolynomial e) (b : BitVec e) : IntegerRing F.f :=
  (coordinate F.f F.monic F.degree).symm fun i => (b.getLsb i).toNat

theorem binaryPoint_residue_injective {e : ℕ} (F : SourcePolynomial e) :
    Function.Injective (fun b => fromInteger F.f 1 (binaryPoint F b)) := by
  intro a b hab
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin e := ⟨i,hi⟩
  have h := congrArg (fun x => wordCoords F.monic F.degree 1 (by decide) x j) hab
  dsimp only at h
  rw [integral_coordinates, integral_coordinates] at h
  have ha : coordinate F.f F.monic F.degree (binaryPoint F a) j = (a.getLsb j).toNat :=
    congrFun ((coordinate F.f F.monic F.degree).apply_symm_apply _) j
  have hb : coordinate F.f F.monic F.degree (binaryPoint F b) j = (b.getLsb j).toNat :=
    congrFun ((coordinate F.f F.monic F.degree).apply_symm_apply _) j
  rw [ha,hb] at h
  change a.getLsb j = b.getLsb j
  cases h₁ : a.getLsb j <;> cases h₂ : b.getLsb j <;>
    rw [h₁, h₂] at h <;> norm_num [integerToWord] at h ⊢
  · change (0 : ZMod 2) = 1 at h
    exact (zero_ne_one h).elim
  · change (1 : ZMod 2) = 0 at h
    exact (one_ne_zero h).elim

theorem probe_unit_difference {e : ℕ} (F : SourcePolynomial e) (p : ℕ) (hp : 0 < p)
    (a b : BitVec e) (hne : a ≠ b) :
    IsUnit (fromInteger F.f p (binaryPoint F a) - fromInteger F.f p (binaryPoint F b)) := by
  apply unit_of_residue_ne_zero F p hp
  rw [map_sub, residue_fromInteger, residue_fromInteger, sub_ne_zero]
  exact fun h => hne (binaryPoint_residue_injective F h)

section FourthPaper
open Entry S11 GraphCutMoments
variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (hn : bigRoot (n (V := V)))

theorem root_probe_unit_difference (F : SourcePolynomial (4*lambda (size E)))
    (t : ℤ) (hp : 0 < nativePrecision E t)
    (i j : Fin (probeCount (rootM E) (rootL E))) (hij : i ≠ j) :
    IsUnit (fromInteger F.f (nativePrecision E t) (binaryPoint F (probe E reg hn i)) -
      fromInteger F.f (nativePrecision E t) (binaryPoint F (probe E reg hn j))) :=
  probe_unit_difference F (nativePrecision E t) hp _ _ (fun h => hij ((probe E reg hn).injective h))

end FourthPaper

#print axioms residue_fromInteger
#print axioms residue_zero_dvd_two
#print axioms probe_unit_difference
#print axioms root_probe_unit_difference

end RootSeparation.Solver
