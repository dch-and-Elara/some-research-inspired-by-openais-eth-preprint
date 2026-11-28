import J6R15ModeCostBlocks
import Mathlib.Algebra.BigOperators.Intervals

/-! Explicit finite-rational count envelope before optimizing over k.
This statement does not count children or bound an evaluator's
recursive time. -/
namespace J6R15ModeCost
open scoped BigOperators
open J6R10Repack

theorem power_antitone_degree (r : ℚ) (hr : 0≤r) (hR : r≤1) {K T : ℕ} (h : K≤T) :
    r^T≤r^K := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hr hR) (pow_nonneg hr _)).trans_eq (mul_one _)

theorem bias_inverse_charge (k K d : ℕ) (hk : 0<k) (h : K≤k*d) :
    ((dyadicBias k)^K)⁻¹≤(2:ℚ)^d := by
  have ⟨hr,hR⟩ := dyadicBias_interval k hk
  have H : (1/2:ℚ)^d≤dyadicBias k^K := by
    calc
      _≤(dyadicBias k^k)^d := pow_le_pow_left₀ (by norm_num) (bias_k_lower k hk) _
      _=dyadicBias k^(k*d) := (pow_mul _ _ _).symm
      _≤_ := power_antitone_degree _ hr.le hR.le h
  have he := inv_anti₀ (show (0:ℚ)<(1/2:ℚ)^d by positivity) H
  have eq : ((1/2:ℚ)^d)⁻¹=(2:ℚ)^d := by
    rw [← inv_pow]
    norm_num
  exact he.trans_eq eq

theorem bias_product_Ico (k p : ℕ) (hk : 0<k) :
    (∏ i ∈ Finset.Ico 1 p,weightFactor (dyadicBias k) i)≤(2:ℚ)^(8*k) := by
  rw [Finset.prod_Ico_eq_prod_range]
  simpa only [Nat.add_comm 1] using biasedProduct_uniform k (p-1) hk

theorem div_succ_fits (K k : ℕ) (hk : 0<k) : K≤k*(K/k+1) := by
  have hd := Nat.mod_add_div K k
  have hm := Nat.mod_lt K hk
  rw [Nat.mul_add,Nat.mul_one]
  omega

theorem native_exponent_bound {E R C G : Type*} [Fintype E] [LinearOrder G] [Fintype G]
    {a p : ℕ} {N : Network E R C} (P : PhysicalPacking N a G) (i : Fin a)
    (ms : List (Mode (Crossing (G:=G) (pages:=P.copies) i) (2^(i.val+1)) p))
    (hm : ms.Nodup) (hall : ∀ m,m∈ms) (hp : 0<p) (k : ℕ) (hk : 0<k) :
    let B := (6*Nat.card E)/2^(a-i.val)
    (strictTuples (ms.map modeWeight) p).length≤2^(8*B*k+((p-1)/k+1)) := by
  have ⟨hR,hI⟩ := dyadicBias_interval k hk
  let B := (6*Nat.card E)/2^(a-i.val)
  let d := (p-1)/k+1
  let q := dyadicBias k
  let U := ∏ j ∈ Finset.Ico 1 p,weightFactor q j
  have h := native_finite_potential P i ms hm hall hp q hR hI
  have hp' : 0≤U := Finset.prod_nonneg (fun j hj => zero_le_one.trans
    (weightFactor_one_le q hR.le hI _ (Finset.mem_Ico.mp hj).1))
  have hU : U^B≤(2:ℚ)^(8*B*k) := by
    have hP := pow_le_pow_left₀ hp' (bias_product_Ico k p hk) B
    rw [← pow_mul] at hP
    convert hP using 1
    ring
  have hD : (q^(p-1))⁻¹≤(2:ℚ)^d := bias_inverse_charge k (p-1) d hk (div_succ_fits _ _ hk)
  have HX : ((strictTuples (ms.map modeWeight) p).length:ℚ)≤(2:ℚ)^(8*B*k+d) := by
    calc
      _≤U^B / q^(p-1) := h
      _=(U^B)*(q^(p-1))⁻¹ := div_eq_mul_inv ..
      _≤(2:ℚ)^(8*B*k)*(2:ℚ)^d :=
        mul_le_mul hU hD (inv_nonneg.mpr (pow_nonneg hR.le _)) (by positivity)
      _=_ := (pow_add ..).symm
  exact_mod_cast HX

#print axioms power_antitone_degree
#print axioms bias_inverse_charge
#print axioms native_exponent_bound
end J6R15ModeCost


