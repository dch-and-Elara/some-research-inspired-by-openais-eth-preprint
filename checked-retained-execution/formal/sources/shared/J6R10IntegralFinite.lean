import J6R10IntegralDeformation

/-! Finite evaluation of the literal localized polynomial. This step
does not reduce a rational polynomial, and does not lift a completed
tensor product to greater precision as if the lift were a ring map. -/
namespace J6R10Integral
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid J6R9Recursive

variable {P K : Type*} [Fintype P] [DecidableEq K] {a : ℕ}

theorem box_two_nil (p : ℕ) (f : ℤ[X]) (ell : ℕ) : (2 : Box f ell p)^p = 0 := by
  simpa only [map_pow,map_ofNat,map_zero] using
    congrArg (J6ActiveInterpolation.scalarIn p f ell) (NativeProbeRing.scalar_nilpotent p f)

theorem scalar_reduces (p : ℕ) (f : ℤ[X]) (ell : ℕ) :
    (reduce p f ell).comp (localScalar f ell) =
      J6ZeroTransport.reduceAt p (box_two_nil p f ell) :=
  J6ZeroTransport.ringHom_unique _ _

noncomputable def finiteEntry (p : ℕ) (f : ℤ[X]) (ell : ℕ) (W : Atlas P K a)
    (t : ℤ) (z : Box f ell p) (i j : P) : Box f ell p :=
  if W.page i = W.page j then
    (J6R9PacketLocal.W a t (W.index j - W.index i)).eval₂
      (J6ZeroTransport.reduceAt p (box_two_nil p f ell)) z
  else 0

omit [Fintype P] in
theorem entry_finite (p : ℕ) (f : ℤ[X]) (ell : ℕ) (W : Atlas P K a)
    (t : ℤ) (z : Box f ell p) (i j : P) :
    ((integralEntry f ell W t i j).map (reduce p f ell)).eval z =
      finiteEntry p f ell W t z i j := by
  unfold integralEntry
  rw [Polynomial.eval_map,Polynomial.eval₂_map,scalar_reduces]
  by_cases h : W.page i = W.page j
  · rw [J6IntegralDeformation.localEntry,finiteEntry,if_pos h,if_pos h]
  · rw [J6IntegralDeformation.localEntry,finiteEntry,if_neg h,if_neg h,eval₂_zero]

/-- Exactly the register value of the original localized network at the
chosen probe, expressed as one ungrouped contraction of all real ports. -/
theorem network_finite (p : ℕ) (f : ℤ[X]) (ell : ℕ) (W : Atlas P K a)
    (t : ℤ) (z : Box f ell p) (U V : (P → Bool) → IntRing f ell) :
    ((integralNetwork f ell W t U V).map (reduce p f ell)).eval z =
      contract (finiteEntry p f ell W t z) ((reduce p f ell) ∘ U) ((reduce p f ell) ∘ V) := by
  rw [integralNetwork,Polynomial.eval_map]
  change (eval₂RingHom (reduce p f ell) z) (contract _ _ _) = _
  rw [map_contract]
  congr 1
  · funext i j
    change (integralEntry f ell W t i j).eval₂ (reduce p f ell) z = _
    rw [← Polynomial.eval_map]
    exact entry_finite p f ell W t z i j
  · funext Y
    exact eval₂_C _ _
  · funext Xb
    exact eval₂_C _ _

/-- Lift each received local tensor entry first, then take their product
as prescribed by the source. This need not equal a lift of the finite
product when observed at higher precision. -/
noncomputable def liftedProduct (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (weights : List (Box f ell p)) : IntRing f ell :=
  (weights.map (canonicalLift p f hf ell)).prod

theorem liftedProduct_at_source (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (weights : List (Box f ell p)) :
    reduce p f ell (liftedProduct p f hf ell weights) = weights.prod := by
  induction weights with
  | nil => simp [liftedProduct]
  | cons x xs ih =>
    simp only [liftedProduct,List.map_cons,List.prod_cons,map_mul,canonicalLift_spec]
    rw [← liftedProduct,ih]

theorem network_origin_after_lifts (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (W : Atlas P K a) (U V : (P → Bool) → List (Box f ell p)) :
    rationalRead p f hf ell
      ((globalNetwork f ell W (liftedProduct p f hf ell ∘ U) (liftedProduct p f hf ell ∘ V)).eval 0) =
      ∑ y, (U y).prod * (V y).prod := by
  rw [network_origin,rationalRead_exact,map_sum]
  simp only [Function.comp_apply,map_mul,liftedProduct_at_source]

theorem network_finite_after_lifts (p q : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (W : Atlas P K a) (t : ℤ) (z : Box f ell q) (U V : (P → Bool) → List (Box f ell p)) :
    ((integralNetwork f ell W t (liftedProduct p f hf ell ∘ U)
        (liftedProduct p f hf ell ∘ V)).map (reduce q f ell)).eval z =
      contract (finiteEntry q f ell W t z)
        (fun y => reduce q f ell (liftedProduct p f hf ell (U y)))
        (fun x => reduce q f ell (liftedProduct p f hf ell (V x))) :=
  network_finite q f ell W t z _ _

#print axioms box_two_nil
#print axioms scalar_reduces
#print axioms entry_finite
#print axioms network_finite
#print axioms liftedProduct_at_source
#print axioms network_origin_after_lifts
#print axioms network_finite_after_lifts
end J6R10Integral
