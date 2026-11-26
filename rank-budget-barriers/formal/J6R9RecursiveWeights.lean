import J6ActivePrintedHermite
import HermiteLossReceive
import Mathlib.Tactic

/-! The two independently verified descriptions of the Appendix D
tapered-Hermite decoder have the very same signed grid, precision, and
rational weights. In particular inactive centres have exponent zero;
removing them from the product changes no multiplier. -/
namespace J6R9Recursive
open scoped BigOperators Polynomial
open Polynomial J6ActiveSchedule J6ActiveUniqueness J6ActiveHermite
  J6ActivePrintedHermite P1DyadicGrid

@[simp] theorem order_same (M u : ℕ) (t : ℤ) :
    order M u t = HermiteLoss.taper u (HermiteLoss.sourceH M u) (HermiteLoss.level t) := rfl

theorem active_grid (a M u : ℕ) {t : ℤ} (ht : t ∈ active a M u) :
    t ∈ grid a ∧ t ≠ 0 := by
  have he := Finset.mem_erase.mp (Finset.mem_filter.mp ht).1
  exact ⟨he.2, he.1⟩

theorem precision_same (p a M u : ℕ) {t : ℤ} (ht : t ∈ active a M u) :
    childPrecision p a M u t = J9PrintedSchedule.precision p (HermiteLoss.sourceH M u)
      (2^(a-HermiteLoss.level t)) M a := by
  have h := active_grid a M u ht
  have hi := HermiteLoss.level_grid_le h.1 h.2
  have hv : (2:ℕ)^a / 2^(HermiteLoss.level t) = 2^(a-HermiteLoss.level t) := by
    have he : (2:ℕ)^a = 2^(a-HermiteLoss.level t) * 2^(HermiteLoss.level t) := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    conv_lhs => rw [he]
    exact Nat.mul_div_cancel _ (pow_pos (by decide) _)
  unfold childPrecision
  exact congrArg (fun d => J9PrintedSchedule.precision p (height M u) d M a) hv

theorem taper_product (a M u : ℕ) (t : ℤ) (f : ℤ → ℚ) :
    (∏ q ∈ (active a M u).erase t, f q ^ order M u q) =
      ∏ q ∈ HermiteLoss.others a t,
        f q ^ HermiteLoss.taper u (HermiteLoss.sourceH M u) (HermiteLoss.level q) := by
  have hsub : (active a M u).erase t ⊆ HermiteLoss.others a t := by
    intro q hq
    obtain ⟨hne,hA⟩ := Finset.mem_erase.mp hq
    have h := active_grid a M u hA
    exact HermiteLoss.mem_others.mpr ⟨h.1,h.2,hne⟩
  simp only [← order_same]
  apply Finset.prod_subset hsub
  intro q hq hn
  obtain ⟨hg,h0,hne⟩ := HermiteLoss.mem_others.mp hq
  have hz : order M u q = 0 := by
    by_contra nh
    exact hn (Finset.mem_erase.mpr ⟨hne,
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨h0,hg⟩, Nat.pos_of_ne_zero nh⟩⟩)
  rw [hz,pow_zero]

variable {K : Type*} [CommRing K] [Algebra ℚ K]

noncomputable def E (a M u : ℕ) (t : ℤ) : K[X] :=
  normalizer (active a M u) (fun q : ℤ => (q:K)) (order M u) invDiff t

noncomputable def extrapolate (a : ℕ) (t : ℤ) : K :=
  (↑(dyadicUnit (R:=K) a)⁻¹ : K) * (-(t:K))

theorem E_zero (a M u : ℕ) (t : ℤ) :
    (E (K:=K) a M u t).eval 0 = algebraMap ℚ K
      ((HermiteLoss.numerator a u (HermiteLoss.sourceH M u) t:ℚ) /
       (HermiteLoss.denominator a u (HermiteLoss.sourceH M u) t:ℚ)) := by
  let n : ℤ → ℚ := fun q => -(q:ℚ)
  let d : ℤ → ℚ := fun q => (t:ℚ)-(q:ℚ)
  have he : (E (K:=K) a M u t).eval 0 = algebraMap ℚ K
      (∏ q ∈ (active a M u).erase t, (n q / d q) ^ order M u q) := by
    unfold E normalizer invDiff
    simp only [eval_prod,eval_pow,eval_mul,eval_C,eval_sub,eval_X,zero_sub,map_prod,
      map_pow,div_eq_mul_inv,map_mul]
    apply Finset.prod_congr rfl
    intro q _
    simp only [n,d,map_neg,map_intCast]
    rw [mul_comm (algebraMap ℚ K _) (-(q:K))]
  rw [he,taper_product]
  congr 1
  simp only [div_pow,Finset.prod_div_distrib,HermiteLoss.numerator,HermiteLoss.denominator,
    Int.cast_prod,Int.cast_pow,Int.cast_neg,Int.cast_sub,n,d]

theorem extrapolate_value (a : ℕ) (t : ℤ) :
    extrapolate (K:=K) a t = algebraMap ℚ K ((-(t:ℚ))/((2:ℚ)^(a+1))) := by
  unfold extrapolate
  change algebraMap ℚ K (((2:ℚ)^(a+1))⁻¹) * (-(t:K)) = _
  rw [div_eq_mul_inv,map_mul,map_neg,map_intCast,mul_comm]

theorem exact_weight (a M u j : ℕ) (t : ℤ) :
    (E (K:=K) a M u t).eval 0 * extrapolate a t ^ j =
      algebraMap ℚ K (HermiteLoss.weight a u (HermiteLoss.sourceH M u) j t) := by
  rw [E_zero,extrapolate_value,← map_pow,← map_mul]
  congr 1
  simp only [HermiteLoss.weight,HermiteLoss.weightNum,HermiteLoss.weightDen,
    Int.cast_mul,Int.cast_pow,Int.cast_neg,HermiteLoss.int_power_rat,div_pow,div_mul_div_comm]

noncomputable def divided (a M u : ℕ) (sample : K[X]) (t : ℤ) : K[X] :=
  dividedJet (order M u t) (atNode (dyadicUnit a) (t:K) (E a M u t)) sample

theorem weighted_sum_one [Nontrivial K] (a M u : ℕ) (sample : K[X]) (t : ℤ)
    (ht : t ∈ active a M u) :
    (E a M u t).eval 0 * (divided a M u sample t).eval (extrapolate a t) =
      ∑ j ∈ Finset.range (order M u t),
        algebraMap ℚ K (HermiteLoss.weight a u (HermiteLoss.sourceH M u) j t) *
          (divided a M u sample t).coeff j := by
  let Q := divided a M u sample t
  have hQ : Q.natDegree < order M u t :=
    dividedJet_degree _ (active_order_pos a M u t ht) _ _
  have hRep := Polynomial.as_sum_range' Q (order M u t) hQ
  change (E a M u t).eval 0 * Q.eval (extrapolate a t) = _
  nth_rw 1 [hRep]
  simp only [eval_finset_sum,eval_monomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← exact_weight]
  ring

theorem exact_origin_weights [Nontrivial K] (a M u : ℕ)
    (hu : 0 < u) (huM : u ≤ M) (F : K[X])
    (hdeg : F.natDegree ≤ J9PrintedSchedule.degreeBound M (2^a))
    (sample : ℤ → K[X]) (hs : ∀ t ∈ active a M u, ∀ j < order M u t,
      (sample t).coeff j = (atNode (dyadicUnit a) (t:K) F).coeff j) :
    (∑ t ∈ active a M u, ∑ j ∈ Finset.range (order M u t),
      algebraMap ℚ K (HermiteLoss.weight a u (HermiteLoss.sourceH M u) j t) *
        (divided a M u (sample t) t).coeff j) = F.eval 0 := by
  calc
    _ = ∑ t ∈ active a M u, (E a M u t).eval 0 *
      (divided a M u (sample t) t).eval (extrapolate a t) :=
      Finset.sum_congr rfl (fun t ht => (weighted_sum_one a M u (sample t) t ht).symm)
    _ = _ := printed_origin a M u hu huM F hdeg sample hs

#print axioms active_grid
#print axioms precision_same
#print axioms taper_product
#print axioms E_zero
#print axioms exact_weight
#print axioms weighted_sum_one
#print axioms exact_origin_weights
end J6R9Recursive