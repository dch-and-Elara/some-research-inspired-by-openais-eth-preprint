import J6R14SpecializedBoxHalfWeight
import J6R14SpecializedBoxModeZero

/-! The finite inverse of the actual odd denominator is supplied as a
specific polynomial in 2*zeta. The actual R12 crossing value therefore
has a canonical normalized polynomial at every prescribed probe,
without guessing its higher tail or using a rational inverse in Box. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators
open Polynomial DenominatorBudget J6R9PacketCoeff J6R9PacketReceive

noncomputable def oddInverse (u : ℤ) (hu : Odd u) : TwoLocal :=
  ⟨(1:ℚ)/(u:ℚ),(mem_twoLocal_iff _).mpr
    ⟨1,u,fun h => (Int.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h),by simp⟩⟩

noncomputable def inverseHalf (a p : ℕ) (u : ℤ) (hu : Odd u) : TwoLocal[X] :=
  C (oddInverse u hu) *
    ∑ j ∈ Finset.range p, (-(C ((2:TwoLocal)^a * oddInverse u hu)*X))^j

noncomputable def modeHalf (a p : ℕ) (t : ℤ) (u : ℤ) (hu : Odd u) (b : ℕ) : TwoLocal[X] :=
  cHatHalf a t * (inverseHalf a p u hu)^(b+1)

section Receive
variable {R : Type*} [CommRing R]

theorem oddInverse_reduces (p : ℕ) (hnil : (2:R)^p=0) (u : ℤ) (hu : Odd u) :
    J6ZeroTransport.reduceAt p hnil (oddInverse u hu) = J6ZeroTransport.oddReciprocal R p u := by
  simpa only [Int.cast_one,one_mul] using
    (J6ZeroTransport.reduce_fraction p hnil (oddInverse u hu) 1 u
      (fun h => (Int.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)) (by simp [oddInverse,twoLocalRat]))

variable {t : ℤ} {x tile : ℕ}

theorem inverseHalf_eval_twice (a p : ℕ) (hnil : (2:R)^p=0)
    (d : Crossing t x tile 0) (z : R) :
    (inverseHalf a p d.oddPart d.odd).eval₂ (J6ZeroTransport.reduceAt p hnil) (2*z) =
      inverseB a p hnil (Nat.zero_le a) d z := by
  let ψ := J6ZeroTransport.reduceAt p hnil
  let E := Polynomial.eval₂RingHom ψ (2*z)
  let w := J6ZeroTransport.oddReciprocal R p d.oddPart
  change E (inverseHalf a p d.oddPart d.odd) = _
  rw [inverseHalf,map_mul,map_sum,valuation_zero_inverse_geometric]
  have hC : E (C (oddInverse d.oddPart d.odd)) = w := by
    change (C (oddInverse d.oddPart d.odd)).eval₂ ψ (2*z) = _
    rw [eval₂_C]
    exact oddInverse_reduces p hnil d.oddPart d.odd
  rw [hC]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _
  change ((-(C ((2:TwoLocal)^a * oddInverse d.oddPart d.odd)*X))^j :
    TwoLocal[X]).eval₂ ψ (2*z) = (-((2:R)^(a+1)*z*w))^j
  simp only [eval₂_pow,eval₂_neg,eval₂_mul,eval₂_C,eval₂_X,eval₂_ofNat,map_mul,map_pow,map_ofNat]
  have hr : ψ (oddInverse d.oddPart d.odd) = w :=
    oddInverse_reduces p hnil d.oddPart d.odd
  rw [hr,pow_succ']
  ring

theorem actual_mode_is_explicit_half_poly (a p : ℕ) (hnil : (2:R)^p=0)
    (d : Crossing t x tile 0) (z : R) (b : ℕ) :
    mode a p hnil (Nat.zero_le a) d z b =
      (2:R)^(a+1+b)*z *
        (modeHalf a p t d.oddPart d.odd b).eval₂ (J6ZeroTransport.reduceAt p hnil) (2*z) := by
  rw [valuation_zero_mode_exact,modeHalf,eval₂_mul,eval₂_pow,cHatHalf_eval_twice,inverseHalf_eval_twice]
  exact mul_assoc _ _ _
end Receive

#print axioms oddInverse
#print axioms inverseHalf
#print axioms modeHalf
#print axioms oddInverse_reduces
#print axioms inverseHalf_eval_twice
#print axioms actual_mode_is_explicit_half_poly
end J6R14SpecializedBox
