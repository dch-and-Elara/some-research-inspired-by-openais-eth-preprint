
import S11Geometric

noncomputable section
namespace S11

open scoped BigOperators
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

private theorem pair_diff_grid {a : ℕ} (x y : Fin (2^a)) :
    (y : ℤ) - (x : ℤ) ∈ grid (2^a) := by
  rw [grid_bounds]
  have hx := x.isLt
  have hy := y.isLt
  have hp : ((2^a:ℕ):ℤ) = (2:ℤ)^a := by push_cast; rfl
  omega

theorem packet_fraction {a : ℕ} (x y : Fin (2^a)) (t : ℤ) (ζ : K) :
    let T := (t:K) + shiftScale K a * ζ
    (packetKernel K (2^a) x y).eval T * (T - (((y:ℤ)-(x:ℤ):ℤ):K)) =
      (shiftedNumerator K a t).eval ζ := by
  dsimp only
  simp only [packetKernel, shiftedNumerator, shiftedFactor, eval_mul,eval_C,eval_prod,
    eval_sub,eval_X,eval_add,mul_assoc]
  rw [Finset.prod_erase_mul _ _ (pair_diff_grid x y)]
  apply congrArg (fun c : K => (originDenominator K (2^a))⁻¹ * c)
  apply Finset.prod_congr rfl
  intro q _
  push_cast
  ring

/-- D's cross-group row entry at the prescribed tile. The hypotheses
    are the native node, equal slot bits across a crossing, and an
    integral probe. Both divisibilities come from the actual kernel. -/
theorem crossing_modes_native (v : AddValuation K (WithTop ℤ)) (h₂ : v (2:K) = 1)
    {a i : ℕ} (hai : i ≤ a) {t : ℤ} (ht : t ∈ grid (2^a)) (ht0 : t ≠ 0)
    (hi : level t = i) (x y : Fin (2^a)) (hb : x.val.testBit i = y.val.testBit i)
    (ζ : K) (hζ : 0 ≤ v ζ) (p : ℕ) (hp : 0 < p) :
    let y0 := y.val % 2^(i+1)
    let j := y.val / 2^(i+1)
    let d := (((t-(y0:ℤ)+x.val:ℤ):K) + shiftScale K a * ζ)
    let base := (shiftedNumerator K a t).eval ζ / d
    let ratio := (2:K)^(i+1) / d
    (∀ b : ℕ, ∃ c : K, 0 ≤ v c ∧ base * ratio^b = 2^(b+1) * c) ∧
      ∃ err : K, 0 ≤ v err ∧
        (packetKernel K (2^a) x y).eval ((t:K)+shiftScale K a*ζ) -
        ∑ b ∈ Finset.range (p-1), base * ratio^b * (j:K)^b = 2^p * err := by
  let y0 := y.val % 2^(i+1)
  let j := y.val / 2^(i+1)
  let d := (((t-(y0:ℤ)+x.val:ℤ):K) + shiftScale K a * ζ)
  let base := (shiftedNumerator K a t).eval ζ / d
  let ratio := (2:K)^(i+1) / d
  let T := (t:K)+shiftScale K a*ζ
  let k := level (t-(y0:ℤ)+x.val)
  have hb' : x.val.testBit i = y0.testBit i := by
    unfold y0
    rw [tile_constant_group_bit]
    exact hb
  obtain ⟨_,hk⟩ := crossing_integer_denominator ht0 hi hb'
  have hd : v d = (↑(k:ℤ) : WithTop ℤ) :=
    crossing_shifted_denominator v h₂ hai ht0 hi hb' ζ hζ
  change k ≤ i at hk
  have hd0 : d ≠ 0 := by
    intro h
    rw [h,v.map_zero] at hd
    exact WithTop.top_ne_coe hd
  have hratio : 1 ≤ v ratio := by
    unfold ratio
    rw [v.map_div,hd,val_two_pow v h₂,← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact_mod_cast (show (1:ℤ) ≤ ((i+1:ℕ):ℤ)-k by omega)
  have hbase : 1 ≤ v base := by
    unfold base
    rw [v.map_div,hd]
    have h := eval_bound v (shifted_numerator_bound v h₂ ht) hζ
    cases hv : v ((shiftedNumerator K a t).eval ζ) with
    | top => simp
    | coe n =>
      rw [hv] at h
      rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
      rw [WithTop.coe_le_coe] at h
      exact_mod_cast (show (1:ℤ) ≤ n-k by omega)
  have hj : 0 ≤ v (j:K) := S7.valuation_nat_nonnegative v j
  have hden : 1-ratio*(j:K) ≠ 0 := by
    have hl : 0 < v (-(ratio*(j:K))) := by
      rw [v.map_neg,v.map_mul]
      exact (by norm_num : (0:WithTop ℤ)<1).trans_le (hratio.trans (le_add_of_nonneg_right hj))
    have hv := valuation_add_strict v (x:=1) (y:= -(ratio*(j:K)))
      (by rwa [v.map_one])
    rw [← sub_eq_add_neg,v.map_one] at hv
    intro he
    rw [he,v.map_zero] at hv
    exact WithTop.top_ne_coe hv
  have hs : (T - (((y:ℤ)-(x:ℤ):ℤ):K)) = d*(1-ratio*(j:K)) := by
    have hy : (y.val:K) = (y0:K) + (2:K)^(i+1)*(j:K) := by
      exact_mod_cast tile_split i y.val
    have hscaled : d*(1-ratio*(j:K)) = d - (2:K)^(i+1)*(j:K) := by
      unfold ratio
      field_simp [hd0]
    rw [hscaled]
    unfold T d
    push_cast
    rw [hy]
    ring
  have hkernel : (packetKernel K (2^a) x y).eval T = base/(1-ratio*(j:K)) := by
    have hh := packet_fraction (K:=K) x y t ζ
    change (packetKernel K (2^a) x y).eval T * _ = _ at hh
    rw [hs] at hh
    apply (eq_div_iff hden).2
    unfold base
    apply (eq_div_iff hd0).2
    convert hh using 1 <;> ring
  refine ⟨fun b => (S7.valuation_threshold v h₂ _ _).1 (coefficient_weight v hbase hratio b), ?_⟩
  change ∃ err : K, 0 ≤ v err ∧ (packetKernel K (2^a) x y).eval T -
      ∑ b ∈ Finset.range (p-1), base*ratio^b*(j:K)^b = 2^p*err
  rw [hkernel]
  exact geometric_remainder v h₂ hbase hratio hj p hp

#print axioms packet_fraction
#print axioms crossing_modes_native

end S11

