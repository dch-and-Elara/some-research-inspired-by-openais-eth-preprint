import J9R14LowPrecisionHalf
import J6R9PacketScaled

/-!
# Finite normalized native kernels in the same residual variable

A public odd denominator is inverted by a finite geometric polynomial
in 2z at precision p. Its powers do not introduce protected bits.
The visible source tariff a+1-i+b is independent of the target row.
-/

namespace J9R14LowPrecisionKernel
open scoped Polynomial Classical BigOperators
open Polynomial DenominatorBudget P1DyadicGrid J6R9PacketCoeff J6R9PacketReceive
open J9R14LowPrecisionHalf

noncomputable section

def oddRecip (u : ℤ) (hu : Odd u) : TwoLocal := by
  have hn : ¬ (2:ℤ) ∣ u := fun h => (Int.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)
  exact ⟨1/(u:ℚ),(mem_twoLocal_iff _).mpr ⟨1,u,hn,by simp⟩⟩

theorem int_mul_recip (u : ℤ) (hu : Odd u) : (u:TwoLocal) * oddRecip u hu = 1 := by
  apply Subtype.ext
  have hn : (u:ℚ)≠0 := by exact_mod_cast odd_int_ne_zero hu
  change (u:ℚ)*(1/(u:ℚ))=1
  field_simp

def inversePoly (a h p : ℕ) (u : ℤ) (hu : Odd u) : TwoLocal[X] :=
  C (oddRecip u hu) *
    ∑ j ∈ Finset.range p,
      Polynomial.monomial j ((-(oddRecip u hu*(2:TwoLocal)^(a-h)))^j)

variable {S : Type*} [CommRing S]
variable {t : ℤ} {x τ i : ℕ}

theorem inverse_poly_correct (a p : ℕ) (hnil : (2:S)^p=0) (hi : i≤a)
    (d : Crossing t x τ i) (z : S) :
    (inversePoly a d.level p d.oddPart d.odd).eval₂ (J6ZeroTransport.reduceAt p hnil) (2*z) =
      inverseB a p hnil hi d z := by
  let ψ := J6ZeroTransport.reduceAt p hnil
  let v := oddRecip d.oddPart d.odd
  let g : TwoLocal[X] := ∑ j ∈ Finset.range p, Polynomial.monomial j ((-(v*(2:TwoLocal)^(a-d.level)))^j)
  have hG : g.eval₂ ψ (2*z) * (1+ψ (v*(2:TwoLocal)^(a-d.level))*(2*z)) = 1 :=
    PrecisionErasure.truncGeom_inverse ψ (v*(2:TwoLocal)^(a-d.level)) z p hnil
  have hD : (d.oddPart:S)*ψ v=1 := by
    simpa only [map_mul,map_one,map_intCast,v] using congrArg ψ (int_mul_recip d.oddPart d.odd)
  have hh : a+1-d.level=(a-d.level)+1 := by have := d.level_le; omega
  have hB : B a d.level d.oddPart z * ψ v = 1+ψ (v*(2:TwoLocal)^(a-d.level))*(2*z) := by
    unfold B
    rw [add_mul,hD,hh,pow_succ,map_mul,map_pow,map_ofNat]
    ring
  have hx : B a d.level d.oddPart z * (inversePoly a d.level p d.oddPart d.odd).eval₂ ψ (2*z)=1 := by
    unfold inversePoly
    change B a d.level d.oddPart z * (C v*g).eval₂ ψ (2*z)=1
    rw [Polynomial.eval₂_mul,Polynomial.eval₂_C,← mul_assoc,hB,mul_comm]
    exact hG
  let z' := (inversePoly a d.level p d.oddPart d.odd).eval₂ ψ (2*z)
  have hy := denominator_inverse_product a p hnil hi d z
  calc
    z' = (B a d.level d.oddPart z * inverseB a p hnil hi d z)*z' := by rw [hy,one_mul]
    _ = inverseB a p hnil hi d z*(B a d.level d.oddPart z*z') := by ring
    _ = _ := by rw [show B a d.level d.oddPart z*z'=1 from hx,mul_one]

def kernelPoly (a p : ℕ) (d : Crossing t x τ i) (b : ℕ) : TwoLocal[X] :=
  C ((2:TwoLocal)^((b+1)*(i-d.level))) *
    (cHatHalf a t*(inversePoly a d.level p d.oddPart d.odd)^(b+1))

/-- One literal selected coefficient, before multiplying the linear
source moment, with exactly the common tariff in manuscript P3. -/
theorem mode_is_public_poly (a p b : ℕ) (hnil : (2:S)^p=0) (hi : i≤a)
    (d : Crossing t x τ i) (z : S) :
    mode a p hnil hi d z b =
      (2:S)^(a+1-i+b)*z*(kernelPoly a p d b).eval₂ (J6ZeroTransport.reduceAt p hnil) (2*z) := by
  let ψ := J6ZeroTransport.reduceAt p hnil
  have hExp : (a+1-d.level)+(i+1-d.level)*b =
      ((a+1-i+b)+(b+1)*(i-d.level)) := by
    have hh := d.level_le
    have h₁ : i+1-d.level = (i-d.level)+1 := by omega
    have h₂ : (a+1-i)+(i-d.level)=(a+1-d.level) := by omega
    rw [h₁,Nat.add_mul,Nat.one_mul,Nat.add_mul,Nat.one_mul]
    rw [Nat.mul_comm b (i-d.level)]
    omega
  unfold mode leading ratio kernelPoly
  rw [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_mul,Polynomial.eval₂_pow,
    cHat_eval_half,inverse_poly_correct a p hnil hi,map_pow,map_ofNat]
  rw [mul_pow,← pow_mul,pow_succ]
  have H : (2:S)^(a+1-d.level)*2^((i+1-d.level)*b)=
      (2:S)^(a+1-i+b)*2^((b+1)*(i-d.level)) := by
    rw [← pow_add,hExp,pow_add]
  linear_combination (z * (cHat a t).eval₂ ψ z * inverseB a p hnil hi d z ^ b * inverseB a p hnil hi d z)*H

#print axioms int_mul_recip
#print axioms inverse_poly_correct
#print axioms mode_is_public_poly

end
end J9R14LowPrecisionKernel
