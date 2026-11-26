import P5P3ExactCriterion
import HermiteLossReflection
import Mathlib.RingTheory.LocalRing.Basic

/-! The native affine geometry is dyadic integer geometry. These
lemmas do not use the full-profile loss sum or the odd-only schedule. -/
namespace Paper5.P3
open P1DyadicGrid HermiteLoss
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

def twoUnit (K : Type*) [Field K] [CharZero K] : Kˣ :=
  Units.mk0 (2:K) (by norm_num)

@[simp] theorem twoUnit_val : (twoUnit K : K) = 2 := rfl

theorem nonneg_two_power (O : Subring K) {n : ℤ} (hn : 0≤n) :
    (↑(twoUnit K^n):K)∈O := by
  rw [←Int.toNat_of_nonneg hn,zpow_natCast,Units.val_pow_eq_pow_val,twoUnit_val]
  have htwo : (2:K)∈O := by
    rw [show (2:K)=1+1 by norm_num]
    exact O.add_mem O.one_mem O.one_mem
  exact O.pow_mem htwo _

theorem two_power_integral_iff (O : Subring K) (hn2 : ¬IsUnit (2:O)) (n : ℤ) :
    (↑(twoUnit K^n):K)∈O ↔ 0≤n := by
  constructor
  · intro h
    by_contra hn
    have hpos : 0 ≤ -n-1 := by omega
    have hh := O.mul_mem h (nonneg_two_power O hpos)
    rw [←Units.val_mul,←zpow_add,show n+(-n-1)=-1 by omega,zpow_neg_one,
      Units.val_inv_eq_inv_val,twoUnit_val] at hh
    let r : O := ⟨(2:K)⁻¹,hh⟩
    have hr : (2:O)*r=1 := by
      apply Subtype.ext
      change (2:K)*(2:K)⁻¹=1
      exact mul_inv_cancel₀ (by norm_num)
    exact hn2 ⟨⟨2,r,hr,by rwa [mul_comm]⟩,rfl⟩
  · exact nonneg_two_power O

omit [CharZero K] in
theorem odd_int_unit (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    {x : ℤ} (hx : Odd x) : ∃ e : Oˣ, (((e:O):K)) = (x:K) := by
  obtain ⟨c,hc⟩ := hx
  have he : 1-(x:O)=(2:O)*(-(c:O)) := by
    rw [hc]
    push_cast
    ring
  have hno : 1-(x:O) ∈ nonunits O := by
    rw [mem_nonunits_iff,he]
    exact fun h => hn2 (isUnit_of_mul_isUnit_left h)
  obtain ⟨u,hu⟩ := IsLocalRing.isUnit_of_mem_nonunits_one_sub_self (x:O) hno
  refine ⟨u,?_⟩
  rw [hu,Subring.coe_intCast]

theorem int_dyadic_unit (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    {x : ℤ} (hx : x≠0) : ∃ e : Oˣ,
    (x:K) = (↑(twoUnit K^(level x:ℤ)):K)*(((e:O):K)) := by
  obtain ⟨z,hz,hxv⟩ := integer_odd_factor hx
  obtain ⟨e,he⟩ := odd_int_unit O hn2 hz
  refine ⟨e,?_⟩
  rw [he,zpow_natCast,Units.val_pow_eq_pow_val,twoUnit_val]
  change x=pow₂ (level x)*z at hxv
  nth_rw 1 [hxv]
  simp [pow₂]

def nativeCenter (a : ℕ) (t : ℤ) : K := (t:K)/(2:K)^(a+1)

theorem nativeCenter_nonzero (a : ℕ) {t : ℤ} (ht : t≠0) : nativeCenter (K:=K) a t≠0 := by
  exact div_ne_zero (by exact_mod_cast ht) (pow_ne_zero _ (by norm_num))

omit [CharZero K] in
theorem nativeCenter_sub (a : ℕ) (r s : ℤ) :
    nativeCenter (K:=K) a r - nativeCenter (K:=K) a s = nativeCenter (K:=K) a (r-s) := by
  unfold nativeCenter
  rw [Int.cast_sub,sub_div]

theorem nativeCenter_injective (a : ℕ) : Function.Injective (nativeCenter (K:=K) a) := by
  intro x y h
  have H := congrArg (fun b : K => b * (2:K)^(a+1)) h
  change (x:K)/(2:K)^(a+1)*(2:K)^(a+1) = (y:K)/(2:K)^(a+1)*(2:K)^(a+1) at H
  simp only [div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num : (2:K)≠0))] at H
  exact_mod_cast H

theorem nativeCenter_unit (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (a : ℕ) {t : ℤ} (ht : t≠0) : ∃ e : Oˣ,
    nativeCenter a t = (↑(twoUnit K^((level t:ℤ)-(a+1:ℕ))):K)*(((e:O):K)) := by
  obtain ⟨w,hw⟩ := int_dyadic_unit O hn2 ht
  refine ⟨w,?_⟩
  unfold nativeCenter
  have hp : (↑(twoUnit K^((a+1:ℕ):ℤ)):K) = (2:K)^(a+1) := by
    rw [zpow_natCast,Units.val_pow_eq_pow_val,twoUnit_val]
  rw [hw,zpow_sub,Units.val_mul,Units.val_inv_eq_inv_val,hp,div_eq_mul_inv]
  ring

theorem inverse_of_native_factor (O : Subring K) {x : K} {z : ℤ} (hz : z≤0)
    (w : Oˣ) (hw : x=(↑(twoUnit K^z):K)*(((w:O):K))) : x⁻¹∈O := by
  have h0 := nonneg_two_power O (n:= -z) (by omega)
  have h1 : x⁻¹ = (↑(twoUnit K^(-z)):K)*((((w⁻¹:Oˣ):O):K)) := by
    rw [hw,mul_inv_rev,zpow_neg,Units.val_inv_eq_inv_val]
    have hh : ((((w⁻¹:Oˣ):O):K)) = ((((w:O):K)))⁻¹ := by
      have hz : (((w:O):K))≠0 := Units.ne_zero (Units.map O.subtype.toMonoidHom w)
      apply mul_left_cancel₀ hz
      rw [←Subring.coe_mul,Units.mul_inv,Subring.coe_one,mul_inv_cancel₀ hz]
    rw [hh,mul_comm]
  rw [h1]
  exact O.mul_mem h0 (Subtype.property _)

theorem nativeCenter_integral_inverses (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (a : ℕ) (t : ℤ) (hmem : t∈grid a) (hn : t≠0) : (nativeCenter (K:=K) a t)⁻¹∈O := by
  obtain ⟨w,hw⟩ := nativeCenter_unit O hn2 a hn
  exact inverse_of_native_factor O (by have h := level_grid_le hmem hn; omega) w hw

theorem nativeDifference_integral_inverses (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (a : ℕ) (r s : ℤ) (hr : r∈grid a) (hs : s∈grid a) :
    (nativeCenter (K:=K) a r-nativeCenter (K:=K) a s)⁻¹∈O := by
  by_cases he : r=s
  · subst s
    simp
  · rw [nativeCenter_sub]
    obtain ⟨w,hw⟩ := nativeCenter_unit O hn2 a (sub_ne_zero.mpr he)
    exact inverse_of_native_factor O (by have h := level_difference_le hr hs he; omega) w hw

#print axioms two_power_integral_iff
#print axioms odd_int_unit
#print axioms int_dyadic_unit
#print axioms nativeCenter_unit
#print axioms nativeCenter_integral_inverses
#print axioms nativeDifference_integral_inverses
end Paper5.P3
