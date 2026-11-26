import S7Precision
import S7Grid

namespace S7
open Finset Polynomial
open scoped BigOperators
noncomputable section
variable {K I : Type*} [Field K]
variable (v : AddValuation K (WithTop ℤ))

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem valuation_nat_nonnegative (n : ℕ) : 0 ≤ v (n:K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (le_min ih (by simp)).trans (v.map_add _ _)

theorem valuation_int_nonnegative (z : ℤ) : 0 ≤ v (z:K) := by
  cases z with
  | ofNat n => simpa using valuation_nat_nonnegative v n
  | negSucc n =>
    rw [Int.cast_negSucc]
    exact (by simpa only [v.map_neg, Nat.cast_succ] using valuation_nat_nonnegative v (n+1))

theorem valuation_odd (h₂ : v (2:K) = 1) (z : ℤ) (hodd : ¬ (2:ℤ) ∣ z) :
    v (z:K) = 0 := by
  have hz : z = 2*(z/2)+1 := by omega
  have hmul : (1:WithTop ℤ) ≤ v (2*((z/2 : ℤ):K)) := by
    rw [v.map_mul, h₂]
    exact le_add_of_nonneg_right (valuation_int_nonnegative v (z/2))
  have hz' : (z:K) - 2*((z/2 : ℤ):K) = 1 := by
    have h := congrArg (Int.castRingHom K) (show z-2*(z/2)=1 by omega)
    simpa only [Int.coe_castRingHom, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using h
  apply le_antisymm _ (valuation_int_nonnegative v z)
  by_contra! hn
  have h := v.map_add (z:K) (-(2*((z/2 : ℤ):K)))
  rw [v.map_neg, ← sub_eq_add_neg, hz', v.map_one] at h
  exact (not_lt_of_ge h) (lt_min hn (lt_of_lt_of_le (by norm_num) hmul))

/-- The normalization v(2)=1 gives the manuscript's v₂ on nonzero integers. -/
theorem valuation_integer (h₂ : v (2:K) = 1) (z : ℤ) (hz : z ≠ 0) :
    v (z:K) = (↑(padicValInt 2 z : ℤ) : WithTop ℤ) := by
  let n := padicValInt 2 z
  obtain ⟨y,hy⟩ := padicValInt_dvd (p:=2) z
  simp only [Nat.cast_ofNat] at hy
  change z = 2^n*y at hy
  have hodd : ¬ (2:ℤ) ∣ y := by
    rintro ⟨k,hk⟩
    have hd : (2:ℤ)^(n+1) ∣ z := ⟨k,by rw [hy,hk,pow_succ,mul_assoc]⟩
    have hp := (padicValInt_dvd_iff (p:=2) (n+1) z).1 (by simpa only [Nat.cast_ofNat] using hd)
    have h := hp.resolve_left hz
    change n+1 ≤ n at h
    omega
  have hz' : (z:K) = 2^n*(y:K) := by
    have h := congrArg (Int.castRingHom K) hy
    simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using h
  rw [hz',v.map_mul, valuation_odd v h₂ y hodd,add_zero,v.map_pow,h₂]
  rw [← WithTop.coe_one, ← WithTop.coe_nsmul]
  simp [n]

/-- A threshold has exactly the meaning of membership in 2^p O. -/
theorem valuation_threshold (h₂ : v (2:K) = 1) (p : ℕ) (z : K) :
    (↑(p:ℤ) : WithTop ℤ) ≤ v z ↔ ∃ u : K, 0 ≤ v u ∧ z = 2^p*u := by
  have hp : v ((2:K)^p) = (↑(p:ℤ) : WithTop ℤ) := by
    rw [v.map_pow,h₂,← WithTop.coe_one,← WithTop.coe_nsmul]
    simp
  have hnz : (2:K)^p ≠ 0 := by
    intro h
    rw [h, v.map_zero] at hp
    exact WithTop.top_ne_coe hp
  constructor
  · intro h
    refine ⟨z/2^p,?_,?_⟩
    · rw [v.map_div,hp]
      cases hv : v z with
      | top => simp
      | coe a =>
        rw [hv] at h
        change ((0:ℤ):WithTop ℤ) ≤ (a:WithTop ℤ) - ((p:ℤ):WithTop ℤ)
        rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_le_coe]
        exact sub_nonneg.mpr (WithTop.coe_le_coe.mp h)
    · field_simp
  · rintro ⟨u,hu,rfl⟩
    rw [v.map_mul,hp]
    exact le_add_of_nonneg_right hu

theorem cast_of_nonzero_int (h₂ : v (2:K) = 1) (z : ℤ) (hz : z ≠ 0) :
    (z:K) ≠ 0 := by
  have h := valuation_integer v h₂ z hz
  intro hh
  rw [hh, v.map_zero] at h
  exact WithTop.top_ne_coe h

def scaledCenter (a : ℕ) (t : ℤ) : K := (t:K)/2^(a+1)

theorem scaledCenter_diff (a : ℕ) (t s : ℤ) :
    scaledCenter (K:=K) a t - scaledCenter a s = scaledCenter a (t-s) := by
  simp only [scaledCenter,Int.cast_sub,sub_div]

theorem valuation_scaledCenter (h₂ : v (2:K) = 1) (a : ℕ) (t : ℤ) (ht : t ≠ 0) :
    v (scaledCenter a t) = (↑((padicValInt 2 t:ℤ)-(a+1:ℕ)) : WithTop ℤ) := by
  rw [scaledCenter,v.map_div,valuation_integer v h₂ t ht,v.map_pow,h₂,← WithTop.coe_one,
    ← WithTop.coe_nsmul]
  have h : (a+1) • (1:ℤ) = ((a+1:ℕ):ℤ) := by simp
  rw [h]
  exact WithTop.LinearOrderedAddCommGroup.coe_sub.symm

theorem scaledCenter_injective (h₂ : v (2:K) = 1) (a : ℕ) :
    Function.Injective (scaledCenter (K:=K) a) := by
  intro t s h
  have he := sub_eq_zero.mpr h
  rw [scaledCenter_diff] at he
  by_contra! hn
  have hv := valuation_scaledCenter v h₂ a (t-s) (sub_ne_zero.mpr hn)
  rw [he,v.map_zero] at hv
  exact WithTop.top_ne_coe hv

variable [Fintype I] [DecidableEq I]

/-- The normalized polynomial C_t has constant valuation equal to the sum
of the physical valuation differences, with the original multiplicities. -/
theorem cardinal_valuation (h₂ : v (2:K) = 1) (a : ℕ)
    (t : I → ℤ) (hinj : Function.Injective t) (hnz : ∀ j, t j ≠ 0)
    (q : I → ℕ) (j : I) :
    v ((cardinal (fun i => scaledCenter a (t i)) q j).eval 0) =
      (↑(∑ i ∈ univ.erase j, (q i : ℤ) *
        ((padicValInt 2 (t i):ℤ)-padicValInt 2 (t j-t i))) : WithTop ℤ) := by
  rw [cardinal,eval_prod]
  have hterm (i : I) (hi : i ∈ univ.erase j) :
      v (eval 0 ((C (scaledCenter a (t j)-scaledCenter a (t i))⁻¹ *
          (X-C (scaledCenter a (t i)))) ^ q i)) =
      (↑((q i:ℤ)*((padicValInt 2 (t i):ℤ)-padicValInt 2 (t j-t i))) : WithTop ℤ) := by
    have hd : t j-t i ≠ 0 := sub_ne_zero.mpr (hinj.ne (Ne.symm (mem_erase.mp hi).1))
    rw [eval_pow,v.map_pow, eval_mul,eval_C,eval_sub,eval_X,eval_C,zero_sub, mul_neg, v.map_neg,
      ← div_eq_inv_mul, v.map_div, scaledCenter_diff, valuation_scaledCenter v h₂ a _ (hnz i),
      valuation_scaledCenter v h₂ a _ hd, ← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_nsmul]
    congr 1
    simp
  generalize (univ.erase j : Finset I) = s at hterm ⊢
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi,prod_insert hi,v.map_mul,hterm _ (mem_insert_self _ _),
      ih (fun k hk => hterm k (mem_insert_of_mem hk)), WithTop.coe_add]

end
end S7
