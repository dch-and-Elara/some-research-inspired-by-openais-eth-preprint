import J6R9RecursiveRings
import J6R9RecursiveWeights
import J6ActiveLocalFactor

/-! The integral E_t(t+αX) and the integral divided jet used by the
receiver are the very polynomials in the exact rational Hermite formula.
All coefficients live in the two literal coefficient quotients. -/
namespace J6R9Recursive
open scoped BigOperators Polynomial
open Polynomial J6ActiveSchedule J6ActiveUniqueness J6ActivePrintedHermite
  J6ActiveHermite J6ActiveLocalFactor DenominatorBudget

noncomputable def integralE (f : ℤ[X]) (ell a M u : ℕ) (t : ℤ) : (IntRing f ell)[X] :=
  (integralNormalizer a (active a M u) (order M u) t).map (localScalar f ell)

theorem integralE_embed (f : ℤ[X]) (ell a M u : ℕ) {t : ℤ}
    (ht : t ∈ active a M u) :
    (integralE f ell a M u t).map (embed f ell) =
      atNode (dyadicUnit a) (t:RatRing f ell) (E a M u t) := by
  let g := algebraMap ℚ (RatRing f ell)
  have hc : (embed f ell).comp (localScalar f ell) = g.comp twoLocalRat :=
    RingHom.ext (embed_localScalar f ell)
  have hgrid (q : ℤ) (hq : q ∈ active a M u) : q ∈ P1DyadicGrid.grid a :=
    (active_grid a M u hq).1
  unfold integralE
  rw [Polynomial.map_map,hc,← Polynomial.map_map,
    integralNormalizer_spec _ _ (hgrid t ht) (fun q hq => hgrid q hq)]
  have hα : (alpha a : ℚ) = (2:ℚ)^(a+1) := rfl
  have ha : (dyadicUnit (R:=RatRing f ell) a : RatRing f ell) = g ((2:ℚ)^(a+1)) := rfl
  simp only [atNode_apply,Polynomial.map_comp,coord,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_X,hα,ha]
  congr 1
  · unfold E normalizer invDiff
    simp only [Polynomial.map_prod,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_sub,
      Polynomial.map_C,Polynomial.map_X,Polynomial.map_intCast,g,map_intCast]

noncomputable def exactQuotient (f : ℤ[X]) (ell a M u : ℕ) (t : ℤ) (F : (IntRing f ell)[X]) :
    (IntRing f ell)[X] :=
  J6ActiveNormalizer.quotientJet (order M u t) (integralE f ell a M u t) F

theorem exactQuotient_embed (f : ℤ[X]) (ell a M u : ℕ) {t : ℤ}
    (ht : t ∈ active a M u) (F : (IntRing f ell)[X]) :
    (exactQuotient f ell a M u t F).map (embed f ell) =
      divided a M u (F.map (embed f ell)) t := by
  rw [exactQuotient, J6ActiveNormalizer.quotientJet_map, integralE_embed f ell a M u ht]
  rfl

theorem weighted_truth_origin (f : ℤ[X]) (ell a M u : ℕ) (hu : 0 < u) (huM : u ≤ M)
    (F : (RatRing f ell)[X]) (hdeg : F.natDegree ≤ J9PrintedSchedule.degreeBound M (2^a))
    (locals : ℤ → (IntRing f ell)[X])
    (integral : ∀ t ∈ active a M u, (locals t).map (embed f ell) =
       atNode (dyadicUnit a) (t:RatRing f ell) F) :
    (∑ t ∈ active a M u, ∑ j ∈ Finset.range (order M u t),
      algebraMap ℚ (RatRing f ell) (HermiteLoss.weight a u (HermiteLoss.sourceH M u) j t) *
        embed f ell ((exactQuotient f ell a M u t (locals t)).coeff j)) = F.eval 0 := by
  nontriviality RatRing f ell
  calc
    _ = ∑ t ∈ active a M u, ∑ j ∈ Finset.range (order M u t),
          algebraMap ℚ (RatRing f ell) (HermiteLoss.weight a u (HermiteLoss.sourceH M u) j t) *
            (divided a M u ((locals t).map (embed f ell)) t).coeff j := by
        refine Finset.sum_congr rfl (fun t ht => Finset.sum_congr rfl (fun j _ => ?_))
        rw [← Polynomial.coeff_map, exactQuotient_embed f ell a M u ht]
    _ = _ := exact_origin_weights a M u hu huM F hdeg _
      (fun t ht j _ => congrArg (fun P : (RatRing f ell)[X] => P.coeff j) (integral t ht))

#print axioms integralE_embed
#print axioms exactQuotient_embed
#print axioms weighted_truth_origin
end J6R9Recursive