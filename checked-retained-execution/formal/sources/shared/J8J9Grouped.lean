import J8EndToEndAmplitude

/-! The denominator-cleared integer of the actual grouped J8 calculation.
The integer sums use the same literal equality and unary pins as the source
ring computation. No congruence or integrality premise is asserted for an
aggregated child or coefficient. -/

namespace J8J9Grouped
open scoped Polynomial BigOperators Classical
open Polynomial DyadicProbeCompiler J8EndToEnd

noncomputable section

section Child
variable {R Ω S : Type*} [Fintype R] [DecidableEq R] [Fintype Ω]
  [Fintype S] [DecidableEq S]

def integerChild (weight : Ω → ℤ) (sign : S → Bool)
    (input : ((S → Bool) × Ω) → R → Bool → ℤ) (mark : Option (R × Bool))
    (feat : ((S → Bool) × Ω) → ℤ) : ℤ :=
  ∑ x : Ω, ∑ bits : S → Bool,
    (∏ i : S, LiteralPortCompiler.truth (R := ℤ)
        (LiteralPortCompiler.pin i (sign i)) bits) * (weight x * feat (bits,x)) *
      ∏ r : R, J8SourceMoment.rowFactor (J8SourceMoment.marker mark r)
        (input (bits,x) r false) (input (bits,x) r true)

theorem integerChild_cast (weight : Ω → ℤ) (sign : S → Bool)
    (input : ((S → Bool) × Ω) → R → Bool → ℤ) (mark : Option (R × Bool))
    (feat : ((S → Bool) × Ω) → ℤ)
    (W : Ω → Source) (base : ((S → Bool) × Ω) → R → Bool → Source[X])
    (feature : ((S → Bool) × Ω) → Source)
    (hw : ∀ x, (weight x : Source) = W x)
    (hb : ∀ x r leg, (input x r leg : Source) = (base x r leg).coeff 0)
    (hf : ∀ x, (feat x : Source) = feature x) :
    (integerChild weight sign input mark feat : Source) =
      (integralChild W sign base mark feature).coeff 0 := by
  let f : ℤ →+* Source := Int.castRingHom Source
  change f (integerChild weight sign input mark feat) = _
  have hW (x : Ω) : f (weight x) = W x := hw x
  have hB (x : (S → Bool) × Ω) (r : R) (leg : Bool) :
      f (input x r leg) = (base x r leg).coeff 0 := hb x r leg
  have hF (x : (S → Bool) × Ω) : f (feat x) = feature x := hf x
  let ev : Source[X] →+* Source := Polynomial.evalRingHom 0
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change _ = ev (integralChild W sign base mark feature)
  have hE (x : (S → Bool) × Ω) (r : R) (leg : Bool) :
      ev (base x r leg) = (base x r leg).coeff 0 := by
    exact (Polynomial.coeff_zero_eq_eval_zero _).symm
  have hC (a : Source) : ev (C a) = a := Polynomial.eval_C
  simp only [integerChild, integralChild, pinWeightSource, map_sum, map_mul, map_prod,
    LiteralPortCompiler.map_truth, J8SourceMoment.map_rowFactor, hW, hB, hF, hE, hC]

end Child

section Completion
variable {I : Type*} [DecidableEq I]

def denominator (s : Finset I) (den : I → ℤ) : ℤ := ∏ i ∈ s, den i

def numerator (s : Finset I) (den : I → ℤ) (scale pub source : ℤ)
    (target : I → ℤ) : ℤ :=
  ∑ i ∈ s, scale * (pub * source * target i) * ∏ j ∈ s.erase i, den j

theorem denominator_positive_odd (s : Finset I) (den : I → ℤ)
    (h : ∀ i ∈ s, 0 < den i ∧ Odd (den i)) :
    0 < denominator s den ∧ Odd (denominator s den) :=
  ⟨Finset.prod_pos (fun i hi => (h i hi).1),
    CoefficientClearing.product_odd _ _ (fun i hi => (h i hi).2)⟩

theorem numerator_cast (s : Finset I) (den : I → ℤ) (scale pub source : ℤ)
    (target : I → ℤ) (h : ∀ i ∈ s, den i ≠ 0) :
    (numerator s den scale pub source target : ℚ) =
      (denominator s den : ℚ) *
        ((pub : ℚ) * source * ∑ i ∈ s, ((scale : ℚ) / den i) * target i) := by
  let t : I → ℤ := fun i => scale * (pub * source * target i)
  have hc := CoefficientClearing.clear_target_sum s t den h
  have hs : (∑ i ∈ s, (t i : ℚ) / den i) =
      ((pub : ℚ) * source) * ∑ i ∈ s, ((scale : ℚ) / den i) * target i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [t, Int.cast_mul]
    ring
  calc
    _ = (denominator s den : ℚ) * ∑ i ∈ s, ((t i : ℤ) : ℚ) / den i := hc.symm
    _ = _ := congrArg (fun z : ℚ => (denominator s den : ℚ) * z) hs

end Completion

#print axioms integerChild_cast
#print axioms denominator_positive_odd
#print axioms numerator_cast

end
end J8J9Grouped
