import J6R9PacketCoeff
import J6ZeroTransport
import Mathlib.Tactic

/-! Real finite-precision crossing packets. The receiving ring may
have zero divisors: we invert only explicitly odd-normalized units.
The omitted range starts at b = p-1, not p. -/
namespace J6R9PacketReceive
open scoped BigOperators Polynomial
open DenominatorBudget J6R9PacketCoeff
variable {R : Type*} [CommRing R]

private theorem two_dvd_pow_mul (e : ℕ) (he : 1 ≤ e) (z : R) :
    (2:R) ∣ (2:R)^e*z := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le he
  refine ⟨(2:R)^k*z,?_⟩
  rw [hk,pow_add,pow_one,mul_assoc]

theorem odd_plus_even_unit (p : ℕ) (hnil : (2:R)^p=0) (u : ℤ) (ho : Odd u)
    (v : R) (hev : (2:R) ∣ v) : IsUnit ((u:R)+v) := by
  have hodd : ¬ (2:ℤ) ∣ u := fun h => (Int.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h)
  obtain ⟨uu,hu⟩ := J6ZeroTransport.oddCast_unit p hnil u hodd
  obtain ⟨r,hr⟩ := hev
  have hN : IsNilpotent ((↑(uu⁻¹) : R)*v) := by
    refine ⟨p,?_⟩
    rw [hr,show (↑(uu⁻¹):R)*(2*r)=2*((↑(uu⁻¹):R)*r) by ring,mul_pow,hnil,zero_mul]
  have he : (u:R)+v=(uu:R)*((↑(uu⁻¹):R)*v+1) := by
    rw [mul_add,mul_one,← mul_assoc,Units.mul_inv,one_mul,hu,add_comm]
  rw [he]
  exact (Units.isUnit uu).mul hN.isUnit_add_one

theorem B_unit {t : ℤ} {x tile i : ℕ} (a p : ℕ) (hnil : (2:R)^p=0)
    (hi : i≤a) (d : Crossing t x tile i) (z : R) :
    IsUnit (B a d.level d.oddPart z) := by
  have hh := d.level_le
  exact odd_plus_even_unit p hnil d.oddPart d.odd _ (two_dvd_pow_mul _ (by omega) _)

noncomputable def inverseB {t : ℤ} {x tile i : ℕ} (a p : ℕ) (hnil : (2:R)^p=0)
    (hi : i≤a) (d : Crossing t x tile i) (z : R) : R :=
  ↑((B_unit a p hnil hi d z).unit⁻¹)

theorem denominator_inverse_product {t : ℤ} {x tile i : ℕ}
    (a p : ℕ) (hnil : (2:R)^p=0) (hi : i≤a) (d : Crossing t x tile i) (z : R) :
    B a d.level d.oddPart z * inverseB a p hnil hi d z = 1 := by
  unfold inverseB
  nth_rewrite 1 [← (B_unit a p hnil hi d z).unit_spec]
  simp

noncomputable def leading {t : ℤ} {x tile i : ℕ} (a p : ℕ) (hnil : (2:R)^p=0)
    (hi : i≤a) (d : Crossing t x tile i) (z : R) : R :=
  (2:R)^(a+1-d.level)*z*(cHat a t).eval₂ (J6ZeroTransport.reduceAt p hnil) z *
    inverseB a p hnil hi d z

noncomputable def ratio {t : ℤ} {x tile i : ℕ} (a p : ℕ) (hnil : (2:R)^p=0)
    (hi : i≤a) (d : Crossing t x tile i) (z : R) : R :=
  (2:R)^(i+1-d.level)*inverseB a p hnil hi d z

noncomputable def mode {t : ℤ} {x tile i : ℕ} (a p : ℕ) (hnil : (2:R)^p=0)
    (hi : i≤a) (d : Crossing t x tile i) (z : R) (b : ℕ) : R :=
  leading a p hnil hi d z * (ratio a p hnil hi d z)^b

private theorem leading_even {t : ℤ} {x tile i : ℕ} (a p : ℕ) (hnil : (2:R)^p=0)
    (hi : i≤a) (d : Crossing t x tile i) (z : R) :
    (2:R) ∣ leading a p hnil hi d z := by
  have hh := d.level_le
  unfold leading
  rw [mul_assoc,mul_assoc]
  exact two_dvd_pow_mul _ (by omega) _

private theorem ratio_even {t : ℤ} {x tile i : ℕ} (a p : ℕ) (hnil : (2:R)^p=0)
    (hi : i≤a) (d : Crossing t x tile i) (z : R) :
    (2:R) ∣ ratio a p hnil hi d z := by
  have hh := d.level_le
  exact two_dvd_pow_mul _ (by omega) _

theorem mode_weight {t : ℤ} {x tile i : ℕ} (a p : ℕ) (hnil : (2:R)^p=0)
    (hi : i≤a) (d : Crossing t x tile i) (z : R) (b : ℕ) :
    (2:R)^(b+1) ∣ mode a p hnil hi d z b := by
  rw [pow_succ']
  exact mul_dvd_mul (leading_even a p hnil hi d z)
    (pow_dvd_pow_of_dvd (ratio_even a p hnil hi d z) b)

private theorem geo (u : R) (n : ℕ) :
    (1-u)*(∑ k ∈ Finset.range n,u^k) = 1-u^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,mul_add,ih,pow_succ]
    ring

theorem weighted_expansion (p : ℕ) (hp : 0<p) (hnil : (2:R)^p=0)
    (c r j : R) (hc : (2:R)∣c) (hr : (2:R)∣r) :
    (1-r*j)*(∑ b ∈ Finset.range (p-1), c*r^b*j^b) = c := by
  have he : (2:R)∣r*j := hr.trans (dvd_mul_right _ _)
  have hD : (2:R)^p ∣ c*(r*j)^(p-1) := by
    have hs : p-1+1=p := Nat.sub_add_cancel hp
    rw [← hs,pow_succ']
    exact mul_dvd_mul hc (pow_dvd_pow_of_dvd he (p-1))
  have hz : c*(r*j)^(p-1)=0 := by
    obtain ⟨z,hz⟩ := hD
    rw [hz,hnil,zero_mul]
  simp_rw [mul_assoc c,← mul_pow,← Finset.mul_sum]
  rw [mul_left_comm,geo,mul_sub,mul_one,hz,sub_zero]

/-- Exact finite-ring crossing readout from the printed coefficients.
No degree or field hypothesis on the receiving ring is present. -/
theorem printed_receive {t : ℤ} {x tile i : ℕ} (a p : ℕ) (hp : 0<p) (hnil : (2:R)^p=0)
    (hi : i≤a) (d : Crossing t x tile i) (z j : R) :
    (B a d.level d.oddPart z-(2:R)^(i+1-d.level)*j) *
      (∑ b ∈ Finset.range (p-1), mode a p hnil hi d z b * j^b) =
    (2:R)^(a+1-d.level)*z*(cHat a t).eval₂ (J6ZeroTransport.reduceAt p hnil) z := by
  let B₀ := B a d.level d.oddPart z
  let u := inverseB a p hnil hi d z
  let N := (2:R)^(a+1-d.level)*z*(cHat a t).eval₂ (J6ZeroTransport.reduceAt p hnil) z
  let v := (2:R)^(i+1-d.level)
  have hInv : B₀*u=1 := denominator_inverse_product a p hnil hi d z
  have h₁ : B₀*(1-(v*u)*j)=B₀-v*j := by
    rw [mul_sub,mul_one,show B₀*(v*u*j)=B₀*u*(v*j) by ring,hInv,one_mul]
  change (B₀-v*j)*(∑ b ∈ Finset.range (p-1), N*u*(v*u)^b*j^b)=N
  have hh : (1-(v*u)*j)*(∑ b ∈ Finset.range (p-1), N*u*(v*u)^b*j^b) = N*u :=
    weighted_expansion p hp hnil _ _ _ (leading_even a p hnil hi d z)
      (ratio_even a p hnil hi d z)
  rw [← h₁,mul_assoc,hh,mul_left_comm B₀ N,hInv,mul_one]

#print axioms B_unit
#print axioms denominator_inverse_product
#print axioms mode_weight
#print axioms weighted_expansion
#print axioms printed_receive
end J6R9PacketReceive
