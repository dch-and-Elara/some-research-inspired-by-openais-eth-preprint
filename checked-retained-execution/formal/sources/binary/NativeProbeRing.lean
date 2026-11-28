import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
import NativeInterpolation

/-! The actual binary-coordinate scalar ring used by the binary-tensor
application (ell=1). We use the same lifted defining polynomial at every
precision, not an arbitrary extension or an assumed unit test. -/

namespace NativeProbeRing
open scoped BigOperators Polynomial
open Polynomial

noncomputable section

abbrev Base (p : ℕ) := ZMod (2^p)

def modTwo (p : ℕ) (hp : 0 < p) : Base p →+* ZMod 2 :=
  ZMod.castHom (show 2 ∣ (2:ℕ)^p from dvd_pow_self _ (by omega)) _

def liftPoly (p : ℕ) (f : ℤ[X]) : (Base p)[X] :=
  f.map (Int.castRingHom _)

def residuePoly (f : ℤ[X]) : (ZMod 2)[X] :=
  f.map (Int.castRingHom _)

abbrev Scalar (p : ℕ) (f : ℤ[X]) := AdjoinRoot (liftPoly p f)
abbrev Residue (f : ℤ[X]) := AdjoinRoot (residuePoly f)

theorem base_nilpotent (p : ℕ) : (2 : Base p)^p = 0 := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2^p)

theorem scalar_nilpotent (p : ℕ) (f : ℤ[X]) : (2 : Scalar p f)^p = 0 := by
  have h := congrArg (AdjoinRoot.of (liftPoly p f)) (base_nilpotent p)
  simpa only [map_pow, map_ofNat, map_zero] using h

theorem map_liftPoly (p : ℕ) (hp : 0 < p) (f : ℤ[X]) :
    (liftPoly p f).map (modTwo p hp) = residuePoly f := by
  rw [liftPoly, Polynomial.map_map, residuePoly]
  congr 1
  ext n
  simp

def residueMap (p : ℕ) (hp : 0 < p) (f : ℤ[X]) : Scalar p f →+* Residue f :=
  AdjoinRoot.lift ((AdjoinRoot.of (residuePoly f)).comp (modTwo p hp))
    (AdjoinRoot.root (residuePoly f)) (by
      rw [← Polynomial.eval₂_map, map_liftPoly]
      exact AdjoinRoot.eval₂_root _)

theorem residue_mk (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (a : (Base p)[X]) :
    residueMap p hp f (AdjoinRoot.mk (liftPoly p f) a) =
      AdjoinRoot.mk (residuePoly f) (a.map (modTwo p hp)) := by
  rw [residueMap, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
  exact AdjoinRoot.aeval_eq _

theorem base_even (p : ℕ) (hp : 0 < p) (a : Base p) (h : modTwo p hp a = 0) :
    2 * (a.val / 2 : ℕ) = a := by
  haveI : NeZero (2^p : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  have e := ZMod.natCast_zmod_val a
  have hz : ((a.val : ℕ) : ZMod 2) = 0 := by
    have q := congrArg (modTwo p hp) e
    simpa only [map_natCast, h] using q
  have hd : 2 ∣ a.val := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hcast := congrArg (fun n : ℕ => (n : Base p)) (Nat.mul_div_cancel' hd)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, e] using hcast

theorem polynomial_even (p : ℕ) (hp : 0 < p) (a : (Base p)[X])
    (h : a.map (modTwo p hp) = 0) : ∃ b, a = C 2 * b := by
  refine ⟨∑ i ∈ a.support, monomial i (((a.coeff i).val / 2 : ℕ) : Base p), ?_⟩
  rw [Finset.mul_sum]
  conv_lhs => rw [a.as_sum_support]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.C_mul_monomial]
  congr 1
  symm
  apply base_even p hp
  have he := congrArg (fun q : (ZMod 2)[X] => q.coeff i) h
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using he

theorem scalar_even (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic)
    (a : Scalar p f) (ha : residueMap p hp f a = 0) : ∃ b, a = 2*b := by
  let hg : (liftPoly p f).Monic := hf.map _
  induction a using AdjoinRoot.induction_on with
  | _ a =>
    rw [residue_mk] at ha
    have hh : (a %ₘ liftPoly p f).map (modTwo p hp) = 0 := by
      rw [Polynomial.map_modByMonic _ hg, map_liftPoly]
      exact (Polynomial.modByMonic_eq_zero_iff_dvd (hf.map _)).mpr
        (AdjoinRoot.mk_eq_zero.mp ha)
    obtain ⟨b, hb⟩ := polynomial_even p hp _ hh
    refine ⟨AdjoinRoot.mk (liftPoly p f) b, ?_⟩
    have hrepr := AdjoinRoot.mk_leftInverse hg (AdjoinRoot.mk (liftPoly p f) a)
    rw [AdjoinRoot.modByMonicHom_mk, hb, map_mul, AdjoinRoot.mk_C, map_ofNat] at hrepr
    exact hrepr.symm

theorem residue_surjective (p : ℕ) (hp : 0 < p) (f : ℤ[X]) :
    Function.Surjective (residueMap p hp f) := by
  intro a
  induction a using AdjoinRoot.induction_on with
  | _ a =>
    have hs : Function.Surjective (modTwo p hp) := ZMod.castHom_surjective _
    obtain ⟨b, hb⟩ := Polynomial.map_surjective _ hs a
    exact ⟨AdjoinRoot.mk _ b, (residue_mk p hp f b).trans (congrArg (AdjoinRoot.mk _) hb)⟩

theorem unit_of_residue (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic)
    [Fact (Irreducible (residuePoly f))]
    (a : Scalar p f) (ha : residueMap p hp f a ≠ 0) : IsUnit a := by
  let r := residueMap p hp f
  obtain ⟨b, hb⟩ := residue_surjective p hp f (r a)⁻¹
  have hz : r (1-a*b) = 0 := by
    rw [map_sub, map_one, map_mul, hb, mul_inv_cancel₀ ha, sub_self]
  obtain ⟨u, hu⟩ := scalar_even p hp f hf (1-a*b) hz
  let x := 1-a*b
  have hx : x^p = 0 := by
    change (1-a*b)^p = 0
    rw [hu, mul_pow, scalar_nilpotent, zero_mul]
  let z := ∑ j ∈ Finset.range p, x^j
  have hg : z*(x-1) = -1 := by
    unfold z
    rw [geom_sum_mul, hx, zero_sub]
  have he : x-1 = -(a*b) := by dsimp [x]; ring
  rw [he, mul_neg, neg_inj] at hg
  have hav : a*(b*z) = 1 := by
    calc
      _ = z*(a*b) := by ring
      _ = 1 := hg
  exact ⟨⟨a,b*z,hav,by rwa [mul_comm]⟩,rfl⟩

/-- The constant coordinate of the unique monic-basis representative. -/
def projectBase (p : ℕ) (f : ℤ[X]) (hf : f.Monic)
    (a : Scalar p f) : Base p :=
  (AdjoinRoot.modByMonicHom (g := liftPoly p f) (hf.map _) a).coeff 0

theorem projectBase_left (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) :
    Function.LeftInverse (projectBase p f hf) (AdjoinRoot.of (liftPoly p f)) := by
  haveI : NeZero (2^p : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  have hN : 1 < (2:ℕ)^p := one_lt_pow₀ (by decide) (by omega)
  letI : Fact (1 < (2:ℕ)^p) := ⟨hN⟩
  intro a
  have hg : (liftPoly p f).Monic := hf.map _
  have he : 0 < (liftPoly p f).natDegree := (hf.natDegree_map (Int.castRingHom (Base p))).symm ▸ hd
  have hc : (C a : (Base p)[X]).degree < (liftPoly p f).degree := by
    apply lt_of_le_of_lt Polynomial.degree_C_le
    rw [Polynomial.degree_eq_natDegree hg.ne_zero]
    exact_mod_cast he
  change (AdjoinRoot.modByMonicHom hg (AdjoinRoot.of (liftPoly p f) a)).coeff 0 = _
  rw [← AdjoinRoot.mk_C, AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff hg).mpr hc, Polynomial.coeff_C_zero]

def binaryPoly (R : Type*) [Semiring R] {e : ℕ} (b : Fin e → Bool) : R[X] :=
  ∑ i : Fin e, monomial i.val (if b i then 1 else 0)

theorem coeff_binaryPoly (R : Type*) [Semiring R] {e : ℕ} (b : Fin e → Bool) (i : Fin e) :
    (binaryPoly R b).coeff i.val = if b i then 1 else 0 := by
  rw [binaryPoly, Polynomial.finset_sum_coeff, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j _ hj
    exact Polynomial.coeff_monomial_of_ne _ (fun h => hj (Fin.ext h.symm))

theorem binaryPoly_degree (R : Type*) [Semiring R] {e : ℕ} (h : 0 < e)
    (b : Fin e → Bool) : (binaryPoly R b).natDegree < e := by
  unfold binaryPoly
  have hl : (∑ i : Fin e, monomial i.val (if b i then (1:R) else 0)).natDegree ≤ e-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le _).trans (by have := i.isLt; omega)
  omega

theorem map_binaryPoly {R S : Type*} [Semiring R] [Semiring S] (r : R →+* S)
    {e : ℕ} (b : Fin e → Bool) : (binaryPoly R b).map r = binaryPoly S b := by
  simp only [binaryPoly, Polynomial.map_sum, Polynomial.map_monomial]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases b i <;> simp

/-- The actual printed binary-coordinate representatives. -/
def probe (p : ℕ) (f : ℤ[X]) (b : Fin f.natDegree → Bool) : Scalar p f :=
  AdjoinRoot.mk (liftPoly p f) (binaryPoly (Base p) b)

theorem binary_residues_injective (p : ℕ) (hp : 0 < p) (f : ℤ[X])
    (hf : f.Monic) (hd : 0 < f.natDegree) :
    Function.Injective (residueMap p hp f ∘ probe p f) := by
  intro a b h
  change residueMap p hp f (probe p f a) = residueMap p hp f (probe p f b) at h
  rw [probe, probe, residue_mk, residue_mk, map_binaryPoly, map_binaryPoly] at h
  have hg : (residuePoly f).Monic := hf.map _
  have dg : (residuePoly f).natDegree = f.natDegree := hf.natDegree_map _
  have red (x : Fin f.natDegree → Bool) :
      (binaryPoly (ZMod 2) x) %ₘ residuePoly f = binaryPoly (ZMod 2) x := by
    apply (Polynomial.modByMonic_eq_self_iff hg).mpr
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    rw [Polynomial.degree_eq_natDegree hg.ne_zero, dg]
    exact_mod_cast binaryPoly_degree (ZMod 2) hd x
  have h' := congrArg (AdjoinRoot.modByMonicHom hg) h
  rw [AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk, red, red] at h'
  funext i
  have hi := congrArg (fun v : (ZMod 2)[X] => v.coeff i.val) h'
  dsimp only at hi
  rw [coeff_binaryPoly, coeff_binaryPoly] at hi
  cases ha : a i <;> cases hb : b i <;> simp_all

/-- This card is exactly the capacity of the printed binary menu. -/
theorem menu_card (e : ℕ) : Fintype.card (Fin e → Bool) = 2^e := by simp

/-- A permitted source order: least-significant coefficient first,
with words visited in binary numeral order. No previously prescribed
external query set is reordered. -/
def chosenRep (e d : ℕ) (_fit : d ≤ 2^e) : Fin d → Fin e → Bool :=
  fun i k => i.val.testBit k.val

theorem chosenRep_injective (e d : ℕ) (fit : d ≤ 2^e) :
    Function.Injective (chosenRep e d fit) := by
  intro i j h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k<e
  · exact congrFun h ⟨k,hk⟩
  · have H : 2^e≤(2:ℕ)^k := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hk)
    rw [Nat.testBit_lt_two_pow (i.isLt.trans_le (fit.trans H)),
      Nat.testBit_lt_two_pow (j.isLt.trans_le (fit.trans H))]

/-- Instantiation of the previous interpolation interface with actual legal
binary lifts, for every requested count within the source menu size. -/
theorem chosenProbes_units (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) [Fact (Irreducible (residuePoly f))]
    (d : ℕ) (fit : d ≤ 2^f.natDegree) :
    let x := fun i => probe p f (chosenRep f.natDegree d fit i)
    ∀ i j : Fin d, i ≠ j → IsUnit (x j - x i) := by
  dsimp only
  intro i j h
  apply unit_of_residue p hp f hf
  rw [map_sub, sub_ne_zero]
  intro eq
  exact h ((chosenRep_injective _ _ _)
    ((binary_residues_injective p hp f hf hd) eq.symm))

/-- For v9's binary entry point ell=1, the extra V quotient really
collapses to the scalar extension, preserving base constants. -/
def truncateOne (R : Type*) [CommRing R] :
    AdjoinRoot (Polynomial.X : R[X]) ≃+* R where
  toFun := AdjoinRoot.lift (RingHom.id R) 0 (by simp)
  invFun := AdjoinRoot.of _
  left_inv := by
    intro x
    induction x using AdjoinRoot.induction_on with
    | _ g =>
      rw [AdjoinRoot.lift_mk, Polynomial.eval₂_id, ← AdjoinRoot.mk_C,
        ← Polynomial.modByMonic_X, ← AdjoinRoot.modByMonicHom_mk Polynomial.monic_X]
      exact AdjoinRoot.mk_leftInverse Polynomial.monic_X _
  right_inv := by
    intro x
    rw [AdjoinRoot.lift_of]
    rfl
  map_mul' := map_mul (AdjoinRoot.lift (RingHom.id R) 0 (by simp))
  map_add' := map_add (AdjoinRoot.lift (RingHom.id R) 0 (by simp))

theorem printed_fit (s ellLog d : ℕ) (hs : s ≤ 2^ellLog) (hd : d ≤ s^4) :
    d ≤ 2^(4*ellLog) := by
  refine hd.trans ?_
  calc
    s^4 ≤ (2^ellLog)^4 := Nat.pow_le_pow_left hs _
    _ = 2^(4*ellLog) := by rw [← pow_mul, Nat.mul_comm ellLog]

/-- Entrywise least lift, deliberately not a ring homomorphism. -/
def raiseCoeff (p q : ℕ) (x : Base p) : Base q := (x.val : Base q)

theorem creation_coeff_stable (p q : ℕ) (h : p ≤ q) (x : Base p) :
    (raiseCoeff p q x).val = x.val := by
  haveI : NeZero (2^p : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  rw [raiseCoeff, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt ((ZMod.val_lt x).trans_le (Nat.pow_le_pow_right (by decide) h))

theorem raiseCoeff_comp (p q r : ℕ) (h : p ≤ q) (x : Base p) :
    raiseCoeff q r (raiseCoeff p q x) = raiseCoeff p r x := by
  unfold raiseCoeff
  exact congrArg (fun a : ℕ => (a : Base r)) (creation_coeff_stable p q h x)

theorem reduce_raised (p q : ℕ) (h : p ≤ q) (x : Base p) :
    ZMod.castHom (pow_dvd_pow (2:ℕ) h) (Base p) (raiseCoeff p q x) = x := by
  haveI : NeZero (2^p : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  rw [raiseCoeff, map_natCast, ZMod.natCast_zmod_val]

/-- The printed coordinate schedule is stable even for a vector of tensor
entries. No arithmetic homomorphism claim is made about raising. -/
theorem creation_vector_stable {ι : Type*} (p q r : ℕ) (h : p ≤ q)
    (x : ι → Base p) :
    (fun i => raiseCoeff q r (raiseCoeff p q (x i))) = fun i => raiseCoeff p r (x i) := by
  funext i
  exact raiseCoeff_comp p q r h (x i)

/-- Exact source check: low-to-high canonical raising is not additive. -/
theorem canonical_raise_not_additive :
    raiseCoeff 2 3 ((3:Base 2)+1) ≠
      raiseCoeff 2 3 (3:Base 2) + raiseCoeff 2 3 1 := by decide

/-- Ring-compatible reduction from a higher precision. This contrasts
with coordinatewise raising, which is deliberately not a ring map. -/
def reduceBase (p q : ℕ) (h : p ≤ q) : Base q →+* Base p :=
  ZMod.castHom (pow_dvd_pow (2:ℕ) h) (Base p)

theorem reduce_liftPoly (p q : ℕ) (h : p ≤ q) (f : ℤ[X]) :
    (liftPoly q f).map (reduceBase p q h) = liftPoly p f := by
  rw [liftPoly, Polynomial.map_map, liftPoly]
  congr 1
  ext n
  simp

def reduceScalar (p q : ℕ) (h : p ≤ q) (f : ℤ[X]) : Scalar q f →+* Scalar p f :=
  AdjoinRoot.lift ((AdjoinRoot.of (liftPoly p f)).comp (reduceBase p q h))
    (AdjoinRoot.root (liftPoly p f)) (by
      rw [← Polynomial.eval₂_map, reduce_liftPoly]
      exact AdjoinRoot.eval₂_root _)

theorem reduceScalar_mk (p q : ℕ) (h : p ≤ q) (f : ℤ[X]) (a : (Base q)[X]) :
    reduceScalar p q h f (AdjoinRoot.mk (liftPoly q f) a) =
      AdjoinRoot.mk (liftPoly p f) (a.map (reduceBase p q h)) := by
  rw [reduceScalar, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
  exact AdjoinRoot.aeval_eq _

theorem same_probe_at_higher_precision (p q : ℕ) (h : p ≤ q) (f : ℤ[X])
    (b : Fin f.natDegree → Bool) :
    reduceScalar p q h f (probe q f b) = probe p f b := by
  rw [probe, probe, reduceScalar_mk, map_binaryPoly]

#print axioms reduceScalar_mk
#print axioms same_probe_at_higher_precision
#print axioms canonical_raise_not_additive
#print axioms creation_coeff_stable
#print axioms raiseCoeff_comp
#print axioms reduce_raised
#print axioms creation_vector_stable
#print axioms truncateOne
#print axioms printed_fit
#print axioms coeff_binaryPoly
#print axioms binary_residues_injective
#print axioms menu_card
#print axioms chosenProbes_units
#print axioms scalar_nilpotent
#print axioms residue_mk
#print axioms scalar_even
#print axioms residue_surjective
#print axioms unit_of_residue
#print axioms projectBase_left

end
end NativeProbeRing