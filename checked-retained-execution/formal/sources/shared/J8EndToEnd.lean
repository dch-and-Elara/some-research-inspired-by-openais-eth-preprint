import DyadicProbeCompiler
import J8PhysicalRecovery

/-!
Finite-ring to rational compatibility in J8. The odd-denominator map is
injective before reduction. Thus the exact cleared integer numerator
itself supplies the reduction compatibility premise; it is not assumed
again after reduction. The normalization exponent is kept explicit.
-/

namespace J8EndToEnd

open scoped Polynomial BigOperators Classical
open NativeProbeRing DyadicProbeCompiler LiteralPortCompiler

noncomputable section

theorem oddRatUnit (u : odds) : IsUnit ((u : ℤ) : ℚ) := by
  apply isUnit_iff_ne_zero.mpr
  have h : (u : ℤ) ≠ 0 := by
    obtain ⟨k,hk⟩ := u.2
    omega
  exact_mod_cast h

def rationalMap : Source →+* ℚ :=
  IsLocalization.lift (M := odds) (g := Int.castRingHom ℚ) oddRatUnit

theorem rationalMap_fraction (n : ℤ) (u : odds) :
    rationalMap (IsLocalization.mk' Source n u) * ((u : ℤ) : ℚ) = (n : ℚ) := by
  rw [mul_comm]
  exact ((IsLocalization.lift_mk'_spec oddRatUnit n
    (rationalMap (IsLocalization.mk' Source n u)) u).mp rfl).symm

theorem rationalMap_injective : Function.Injective rationalMap := by
  have zeroKernel (x : Source) (hx : rationalMap x = 0) : x = 0 := by
    obtain ⟨n,u,rfl⟩ := IsLocalization.mk'_surjective odds x
    have h := rationalMap_fraction n u
    rw [hx, zero_mul] at h
    have hn : n = 0 := by exact_mod_cast h.symm
    subst n
    exact IsLocalization.mk'_zero u
  intro x y h
  apply sub_eq_zero.mp
  apply zeroKernel
  rw [map_sub, h, sub_self]

def scaledValue (p : ℕ) (f : ℤ[X]) (e : ℕ) (q0 : Source) : Scalar p f :=
  (2 : Scalar p f)^e * toScalar p f q0

/-- The actual integer equality over ℚ forces the cleared residue equality
in the source finite extension. No separately assumed lifted equality. -/
theorem clearing_reduces (p : ℕ) (f : ℤ[X]) (e : ℕ) (q0 : Source) (D a : ℤ)
    (exact_num : (a : ℚ) = (D : ℚ) * ((2 : ℚ)^e * rationalMap q0)) :
    (D : Scalar p f) * scaledValue p f e q0 =
      AdjoinRoot.of (liftPoly p f) (a : Base p) := by
  have heq : (D : Source) * ((2 : Source)^e * q0) = (a : Source) := by
    apply rationalMap_injective
    simpa only [map_mul, map_pow, map_intCast, map_ofNat] using exact_num.symm
  unfold scaledValue
  calc
    _ = toScalar p f ((D : Source) * ((2 : Source)^e * q0)) := by
      simp only [map_mul, map_pow, map_intCast, map_ofNat]
    _ = _ := by
      rw [heq, map_intCast, map_intCast]

/-- Decode the first coefficient after it has been obtained in the finite
ring, using its original clearing factor. The remaining numeric premise
is exactly the centered representative bound, not injectivity of ℚ→R. -/
def readRational (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (D : ℤ) (value : Scalar p f) : ℚ :=
  ((projectBase p f hf ((D : Scalar p f) * value)).valMinAbs : ℚ) / (D : ℚ)

theorem lift_observed_first (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) (e : ℕ) (q0 : Source) (D a : ℤ) (hD : D ≠ 0)
    (fits : a*2 ∈ Set.Ioc (-(↑((2:ℕ)^p)) : ℤ) ↑((2:ℕ)^p))
    (exact_num : (a : ℚ) = (D : ℚ) * ((2 : ℚ)^e * rationalMap q0)) :
    readRational p f hf D (scaledValue p f e q0) = (2 : ℚ)^e * rationalMap q0 := by
  haveI : NeZero (2^p : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  unfold readRational
  rw [clearing_reduces p f e q0 D a exact_num, projectBase_left p hp f hf hd]
  have hval := (ZMod.valMinAbs_spec (a : Base p) a).mpr ⟨rfl, fits⟩
  rw [hval, exact_num]
  apply mul_div_cancel_left₀
  exact_mod_cast hD

section Literal

variable {P M : Type*} [Fintype P] [DecidableEq P] [Fintype M] [DecidableEq M]

/-- Actual finite compiled singleton samples and the signed representative
readout, not a hypothesis about a desired output of interpolation. -/
theorem literal_compiler_lift
    (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))] (fit : p+1 ≤ 2^f.natDegree)
    (F : CNF P) (base : (P → Bool) → P → Source[X])
    (kernel : (P → Bool) → P → M → Source[X])
    (e : M → ℕ) (m : M) (hv : 1 ≤ e m)
    (D a : ℤ) (hD : D ≠ 0)
    (fits : a*2 ∈ Set.Ioc (-(↑((2:ℕ)^p)) : ℤ) ↑((2:ℕ)^p))
    (exact_num : (a : ℚ) = (D : ℚ) * ((2:ℚ)^e m *
      rationalMap ((MvPolynomial.coeff (Finsupp.single m 1) (completed F base kernel)).coeff 0))) :
    let φ := toScalar p f
    let x := fun i => probe p f (chosenRep f.natDegree (p+1) fit i)
    let β := Finsupp.single m 1
    let q := MvPolynomial.coeff β (completed F base kernel)
    let samples := fun i => MvPolynomial.coeff β
      (completed F (fun a j => (base a j).eval₂ φ (2*x i))
        (fun a j k => (2 : Scalar p f)^e k * x i * (kernel a j k).eval₂ φ (2*x i)))
    readRational p f hf D (NativeInterpolation.decode x samples ⟨1,by omega⟩) =
      (2:ℚ)^e m * rationalMap (q.coeff 0) := by
  dsimp only
  rw [DyadicProbeCompiler.decode_source p hp f hf hd fit F base kernel e m hv]
  exact lift_observed_first p hp f hf hd (e m) _ D a hD fits exact_num

end Literal

section Grouped

variable {I : Type*}

def groupedNormalized (s : Finset I) (pub src : Source[X])
    (target normKernel : I → Source[X]) : Source[X] :=
  (pub * src) * ∑ j ∈ s, normKernel j * target j

/-- The actual grouped root slot is evaluated by multiplying child
contractions at the given probe. The singleton contributes one explicit
power of the probe and its full dyadic factor. -/
def groupedProbe (p : ℕ) (f : ℤ[X]) (e : ℕ) (s : Finset I) (pub src : Source[X])
    (target normKernel : I → Source[X]) (z : Scalar p f) : Scalar p f :=
  let eval := fun q : Source[X] => q.eval₂ (toScalar p f) (2*z)
  (eval pub * eval src) *
    ∑ j ∈ s, ((2 : Scalar p f)^e * z * eval (normKernel j)) * eval (target j)

theorem groupedProbe_normalized (p : ℕ) (f : ℤ[X]) (e : ℕ) (s : Finset I)
    (pub src : Source[X]) (target normKernel : I → Source[X]) (z : Scalar p f) :
    groupedProbe p f e s pub src target normKernel z =
      (NativeInterpolation.normalized p e 1
        (fun j => toScalar p f ((groupedNormalized s pub src target normKernel).coeff j))).eval z := by
  let φ := toScalar p f
  let q := groupedNormalized s pub src target normKernel
  have h :
      groupedProbe p f e s pub src target normKernel z =
        (2 : Scalar p f)^e * z * q.eval₂ φ (2*z) := by
    let ψ : Source[X] →+* Scalar p f := Polynomial.eval₂RingHom φ (2*z)
    change (ψ pub * ψ src) * (∑ j ∈ s, ((2 : Scalar p f)^e * z * ψ (normKernel j)) *
        ψ (target j)) = (2 : Scalar p f)^e * z * ψ q
    simp only [q, groupedNormalized, map_mul, map_sum, mul_assoc, ← Finset.mul_sum]
    ring
  rw [h, DyadicSlotCompiler.eval_truncation φ q p z (scalar_nilpotent p f),
    NativeInterpolation.normalized_eval, pow_one]

/-- Finite interpolation for the already compiled grouped source/target
polynomial, at any distinct real binary probe addresses. -/
theorem grouped_decode_binary
    (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))] (e : ℕ) (he : 1 ≤ e)
    (addr : Fin (p+1) → Fin f.natDegree → Bool) (distinct : Function.Injective addr)
    (s : Finset I) (pub src : Source[X]) (target normKernel : I → Source[X]) :
    let x := fun j => probe p f (addr j)
    NativeInterpolation.decode x
      (fun j => groupedProbe p f e s pub src target normKernel (x j)) ⟨1,by omega⟩ =
        scaledValue p f e ((groupedNormalized s pub src target normKernel).coeff 0) := by
  dsimp only
  simp_rw [groupedProbe_normalized]
  apply NativeInterpolation.singleton_from_completed_probes p e _ hp he (scalar_nilpotent p f)
  apply NativeInterpolation.unit_differences_from_residue (residueMap p hp f)
    (unit_of_residue p hp f hf)
  exact ((binary_residues_injective p hp f hf hd).comp distinct)

end Grouped

#print axioms rationalMap_injective
#print axioms clearing_reduces
#print axioms lift_observed_first
#print axioms literal_compiler_lift
#print axioms groupedProbe_normalized
#print axioms grouped_decode_binary

end
end J8EndToEnd
