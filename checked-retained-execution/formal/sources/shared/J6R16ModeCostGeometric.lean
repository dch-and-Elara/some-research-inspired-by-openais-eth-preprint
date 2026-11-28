import J1PPrintedDepth
import Mathlib.Algebra.BigOperators.Intervals

/-! Integer depth summation. Replace the true shrink ratio sqrt(2)/8
by the slightly looser 1/4, without dropping floor precision or
counting prefix choices as emitted children. -/
namespace J6R16ModeCost
open scoped BigOperators
open J1PPrinted

def depthScale (s C lam K : ℕ) : ℕ :=
  Nat.sqrt ((12*K*epsDen*(C*s)*(C*s))/lam)

def depthExponent (s C lam K d : ℕ) : ℕ :=
  18*(depthScale s C lam K/4^d)

theorem depth_sqrt_le (s C lam K d M u : ℕ)
    (hLam : 0<lam) (hu : 0<u)
    (hFloor : lam≤(2*epsDen*2^d)*u) (hM : 8^d*M≤C*s) :
    Nat.sqrt ((6*K*M*M)/u)≤depthScale s C lam K/4^d := by
  let E := Nat.sqrt ((6*K*M*M)/u)
  have hE : (E*E)*u≤6*K*M*M :=
    (Nat.le_div_iff_mul_le hu).mp (Nat.sqrt_le _)
  have hPow : ((4:ℕ)^d)*4^d*2^d≤8^d*8^d := by
    calc
      _=(4*4*2:ℕ)^d := by rw [mul_pow,mul_pow]
      _≤(8*8:ℕ)^d := Nat.pow_le_pow_left (by decide) _
      _=_ := mul_pow _ _ _
  have H : ((E*4^d)*(E*4^d))*lam≤12*K*epsDen*(C*s)*(C*s) := by
    calc
      _≤((E*4^d)*(E*4^d))*((2*epsDen*2^d)*u) := Nat.mul_le_mul_left _ hFloor
      _=(2*epsDen)*((4^d*4^d*2^d)*((E*E)*u)) := by ring
      _≤(2*epsDen)*((8^d*8^d)*(6*K*M*M)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hPow hE)
      _=(12*K*epsDen)*((8^d*M)*(8^d*M)) := by ring
      _≤_ := by
        convert Nat.mul_le_mul_left (12*K*epsDen) (Nat.mul_le_mul hM hM) using 1
        ring
  apply (Nat.le_div_iff_mul_le (by positivity : 0<(4:ℕ)^d)).mpr
  apply Nat.le_sqrt.mpr
  exact (Nat.le_div_iff_mul_le hLam).mpr H

theorem quarter_sum (X h : ℕ) : 3*(∑ d∈Finset.range h,X/4^d)≤4*X := by
  induction h generalizing X with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ',pow_zero,Nat.div_one]
    have e (d : ℕ) : X/(4:ℕ)^(d+1)=(X/4)/4^d := by
      rw [Nat.div_div_eq_div_mul,pow_succ',Nat.mul_comm 4 (4^d)]
    simp_rw [e]
    have H := ih (X/4)
    have H' := Nat.div_mul_le_self X 4
    omega

theorem depth_exponents_sum (s C lam K h : ℕ) :
    (∑ d∈Finset.range h,depthExponent s C lam K d)≤24*depthScale s C lam K := by
  unfold depthExponent
  rw [← Finset.mul_sum]
  have H := quarter_sum (depthScale s C lam K) h
  omega

theorem depth_product (s C lam K b h : ℕ) :
    (∏ d∈Finset.range h,(2:ℕ)^(b+depthExponent s C lam K d))≤
      2^(b*h+24*depthScale s C lam K) := by
  rw [Finset.prod_pow_eq_pow_sum,Finset.sum_add_distrib]
  apply Nat.pow_le_pow_right (by decide)
  have e : (∑ _ ∈ Finset.range h,b)=b*h := by simp [Nat.mul_comm]
  rw [e]
  exact Nat.add_le_add_left (depth_exponents_sum s C lam K h) (b*h)

#print axioms depth_sqrt_le
#print axioms quarter_sum
#print axioms depth_exponents_sum
#print axioms depth_product
end J6R16ModeCost


