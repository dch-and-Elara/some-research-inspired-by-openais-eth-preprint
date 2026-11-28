import J8EndToEnd

/-!
The remaining J8 algebraic bridge. First coefficients are matched by each
original local row argument and selected target kernel separately, not by
assuming equality of the whole finite observed coefficient.
-/

namespace J8EndToEnd

open scoped BigOperators Polynomial Classical
open Polynomial NativeProbeRing DyadicProbeCompiler

noncomputable section

section Child

variable {R Ω S : Type*}
variable [Fintype R] [DecidableEq R] [Fintype Ω] [Fintype S] [DecidableEq S]

def pinWeightSource (sign bits : S → Bool) : Source :=
  ∏ i : S, LiteralPortCompiler.truth (LiteralPortCompiler.pin i (sign i)) bits

omit [DecidableEq S] in
theorem pinWeightSource_rational (sign bits : S → Bool) :
    rationalMap (pinWeightSource sign bits) = J8SourceMoment.pinWeight sign bits := by
  unfold pinWeightSource J8SourceMoment.pinWeight
  rw [map_prod]
  exact Finset.prod_congr rfl (fun _ _ => LiteralPortCompiler.map_truth rationalMap _ _)

def integralChild (weight : Ω → Source) (sign : S → Bool)
    (base : ((S → Bool) × Ω) → R → Bool → Source[X]) (mark : Option (R × Bool))
    (feature : ((S → Bool) × Ω) → Source) : Source[X] :=
  ∑ x : Ω, ∑ bits : S → Bool,
    C (pinWeightSource sign bits * (weight x * feature (bits,x))) *
      ∏ r : R, J8SourceMoment.rowFactor (J8SourceMoment.marker mark r)
        (base (bits,x) r false) (base (bits,x) r true)

/-- Gauge/higher-order choices disappear from every compiled child constant.
The only premises concern original nonpin weights, actual tile bits, and
the scalar at each physical row input. -/
theorem child_const_matches (d : J8SourceMoment.Child R Ω)
    (weight : Ω → Source) (sign : S → Bool)
    (base : ((S → Bool) × Ω) → R → Bool → Source[X])
    (higher : ((S → Bool) × Ω) → R → Bool → ℚ[X])
    (mark : Option (R × Bool))
    (feature : ((S → Bool) × Ω) → Source) (actualFeature : ((S → Bool) × Ω) → ℚ)
    (weights : ∀ x, rationalMap (weight x) = d.oldWeight x)
    (features : ∀ X, rationalMap (feature X) = actualFeature X)
    (inputs : ∀ X r leg, rationalMap ((base X r leg).coeff 0) =
      J8SourceMoment.input0 d X.2 r leg) :
    rationalMap ((integralChild weight sign base mark feature).coeff 0) =
      (J8SourceMoment.genuineChild d sign higher mark actualFeature).coeff 0 := by
  let ev : Source[X] →+* ℚ := rationalMap.comp (Polynomial.evalRingHom 0)
  have hbase (X : (S → Bool) × Ω) (r : R) (leg : Bool) :
      ev (base X r leg) = J8SourceMoment.input0 d X.2 r leg := by
    change rationalMap ((base X r leg).eval 0) = _
    rw [← Polynomial.coeff_zero_eq_eval_zero, inputs]
  have hc (w : Source) : ev (C w) = rationalMap w := by
    change rationalMap ((C w).eval 0) = _
    rw [Polynomial.eval_C]
  rw [J8SourceMoment.childConstant, Polynomial.coeff_zero_eq_eval_zero]
  change ev (integralChild weight sign base mark feature) = _
  simp only [integralChild, map_sum, map_mul, map_prod, J8SourceMoment.map_rowFactor,
    hc, hbase, weights, features, pinWeightSource_rational, J8SourceMoment.pinWeight_iff]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq', J8SourceMoment.weighted]
  ring

end Child

section Completion

variable {I : Type*}

/-- Compare the rescaled constant to the genuine rational first coefficient
using only a constant equality at each source/target/ordinary child and
the one-port normalized kernels. -/
theorem grouped_first_matches (e : ℕ) (s : Finset I)
    (pub src : Source[X]) (target normKernel : I → Source[X])
    (rPub rSrc : ℚ[X]) (rTarget rKernel : I → ℚ[X])
    (public_const : rationalMap (pub.coeff 0) = rPub.coeff 0)
    (source_const : rationalMap (src.coeff 0) = rSrc.coeff 0)
    (target_const : ∀ j ∈ s, rationalMap ((target j).coeff 0) = (rTarget j).coeff 0)
    (scaled_kernel : ∀ j ∈ s, (2:ℚ)^e * rationalMap ((normKernel j).coeff 0) =
       (rKernel j).coeff 1)
    (vanishing : ∀ j ∈ s, (rKernel j).coeff 0 = 0) :
    (2:ℚ)^e * rationalMap ((groupedNormalized s pub src target normKernel).coeff 0) =
      (NativeCompletedRecovery.completed s rPub rSrc rKernel rTarget).coeff 1 := by
  rw [NativeCompletedRecovery.completed,
    TargetDerivative.first_completed_target _ _ _ _ _ vanishing]
  have hsum : (2:ℚ)^e * (∑ j ∈ s, rationalMap ((normKernel j).coeff 0) *
      rationalMap ((target j).coeff 0)) =
    ∑ j ∈ s, (rKernel j).coeff 1 * (rTarget j).coeff 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, scaled_kernel j hj, target_const j hj]
  simp only [groupedNormalized, Polynomial.mul_coeff_zero, Polynomial.finset_sum_coeff,
    map_mul, map_sum, public_const, source_const]
  rw [show (2:ℚ)^e * ((rPub.coeff 0 * rSrc.coeff 0) *
       ∑ j ∈ s, rationalMap ((normKernel j).coeff 0) *
        rationalMap ((target j).coeff 0)) =
      (rPub.coeff 0 * rSrc.coeff 0) *
       ((2:ℚ)^e * ∑ j ∈ s, rationalMap ((normKernel j).coeff 0) *
        rationalMap ((target j).coeff 0)) by ac_rfl, hsum]
  ac_rfl

/-- Putting interpolation, localization clearing and the physical rational
first coefficient into a single equality for one actual grouped slot. -/
theorem grouped_read_compares
    (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))] (e : ℕ) (he : 1 ≤ e)
    (addr : Fin (p+1) → Fin f.natDegree → Bool) (distinct : Function.Injective addr)
    (s : Finset I) (pub src : Source[X]) (target normKernel : I → Source[X])
    (rPub rSrc : ℚ[X]) (rTarget rKernel : I → ℚ[X])
    (public_const : rationalMap (pub.coeff 0) = rPub.coeff 0)
    (source_const : rationalMap (src.coeff 0) = rSrc.coeff 0)
    (target_const : ∀ j ∈ s, rationalMap ((target j).coeff 0) = (rTarget j).coeff 0)
    (scaled_kernel : ∀ j ∈ s, (2:ℚ)^e * rationalMap ((normKernel j).coeff 0) =
       (rKernel j).coeff 1)
    (vanishing : ∀ j ∈ s, (rKernel j).coeff 0 = 0)
    (D a : ℤ) (hD : D ≠ 0)
    (fits : a*2 ∈ Set.Ioc (-(↑((2:ℕ)^p)) : ℤ) ↑((2:ℕ)^p))
    (exact_num : (a : ℚ) = D * (NativeCompletedRecovery.completed s rPub rSrc rKernel rTarget).coeff 1) :
    let x := fun j => probe p f (addr j)
    readRational p f hf D (NativeInterpolation.decode x
      (fun j => groupedProbe p f e s pub src target normKernel (x j)) ⟨1,by omega⟩) =
        (NativeCompletedRecovery.completed s rPub rSrc rKernel rTarget).coeff 1 := by
  dsimp only
  have eq := grouped_first_matches e s pub src target normKernel rPub rSrc rTarget rKernel
    public_const source_const target_const scaled_kernel vanishing
  rw [grouped_decode_binary p hp f hf hd e he addr distinct s pub src target normKernel,
    lift_observed_first p hp f hf hd e _ D a hD fits (by rw [eq, ← exact_num]), eq]

end Completion

#print axioms child_const_matches
#print axioms grouped_first_matches
#print axioms grouped_read_compares

end
end J8EndToEnd
