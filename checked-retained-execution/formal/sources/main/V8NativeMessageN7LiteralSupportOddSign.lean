import V8NativeMessageN7LiteralSupportSigned
import J6NativeHeightDerivative

/-! The sign at every signed odd grid centre, including the negative
outer half of the literal grid. This is a rational statement. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Polynomial
open Polynomial P1DyadicGrid P1DyadicGridBridge
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

theorem odd_centres_have_negative_actual_scalar {a : ℕ} {t : ℤ}
    (mem : t∈grid a) (odd : Odd t) : (derivRatio a t:ℚ)<0 := by
  obtain ⟨z,e⟩ := odd
  by_cases s : 0≤t
  · let k := t.toNat
    have eq : (k:ℤ)=t := Int.toNat_of_nonneg s
    have q : (k:ℤ)<(2:ℤ)^a := by
      rw [eq]
      exact (mem_grid.mp mem).2
    have bound : k<2^a := by exact_mod_cast q
    have oddK : Odd k := by
      refine ⟨z.toNat,?_⟩
      omega
    rw [←eq,J6NativeHeightDerivative.ratio_eq_grid a k bound,oddK.neg_one_pow,neg_one_mul]
    exact neg_lt_zero.mpr (LayerRecovery.gridRatio_pos bound)
  · let k := (-1-t).toNat
    have eq : (k:ℤ)=-1-t := Int.toNat_of_nonneg (by omega)
    have q : (k:ℤ)<(2:ℤ)^a := by
      rw [eq]
      exact (mem_grid.mp (reflected_grid mem)).2
    have bound : k<2^a := by exact_mod_cast q
    have evenK : Even k := by
      refine ⟨(-z-1).toNat,?_⟩
      omega
    have sign := derivative_ratio_reflected mem
    rw [←eq,J6NativeHeightDerivative.ratio_eq_grid a k bound,evenK.neg_one_pow,one_mul] at sign
    have pos := LayerRecovery.gridRatio_pos bound
    linarith

end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.odd_centres_have_negative_actual_scalar
