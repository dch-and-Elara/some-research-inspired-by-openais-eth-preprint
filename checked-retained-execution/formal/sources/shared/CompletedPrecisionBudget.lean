import CoefficientClearing
import Mathlib.Tactic

/-! J9 explicit sufficient finite precision for a cleared completed singleton.
The theorem bounds the actual signed sum, not just a nonnegative surrogate.
The public geometry must supply the enumerator and its cardinality bounds. -/

namespace CompletedPrecisionBudget
open scoped BigOperators

variable {I A : Type*} [DecidableEq I]

noncomputable def cleared (s : Finset I) (a : Finset A) (d : I → ℤ)
    (slopeNum : I → ℤ) (term : I → A → ℤ) : ℤ :=
  ∑ i ∈ s, ∑ x ∈ a, slopeNum i * term i x * ∏ j ∈ s.erase i, d j

theorem cleared_correct (s : Finset I) (a : Finset A) (d slopeNum : I → ℤ)
    (term : I → A → ℤ) (hd : ∀ i ∈ s, d i ≠ 0) :
    (cleared s a d slopeNum term : ℚ) =
      ((∏ i ∈ s, d i : ℤ) : ℚ) *
        (∑ i ∈ s, ((slopeNum i * (∑ x ∈ a, term i x) : ℤ) : ℚ) / d i) := by
  rw [CoefficientClearing.clear_target_sum _ _ _ hd]
  unfold cleared
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_mul]

/-- `ell` bounds each positive denominator root and the number of target
ports by a power of two. `b` is the singleton mode's exponent parameter.
The term comprises the source moment, the exceptional derivative and the
remaining contracted baseline factors. -/
def overhead (L b ell eSlope : ℕ) : ℕ :=
  ell + eSlope + (b+1)*ell + (2*L+1) + L*((b+1)*ell)

theorem centered_10M (s : Finset I) (a : Finset A)
    (d slopeNum : I → ℤ) (moment derivative baseline : I → A → ℤ)
    (M L b ell k eSlope : ℕ)
    (hs : s.card ≤ L) (hL : L ≤ 2^ell) (ha : a.card ≤ 2^M)
    (hk : L*k ≤ 3*M)
    (hd : ∀ i ∈ s, |d i| ≤ 2^((b+1)*ell))
    (hS : ∀ i ∈ s, |slopeNum i| ≤ 2^eSlope)
    (hMoment : ∀ i ∈ s, ∀ x ∈ a, |moment i x| ≤ 2^((b+1)*ell))
    (hDeriv : ∀ i ∈ s, ∀ x ∈ a, |derivative i x| ≤ 2^(2*L+1))
    (hBase : ∀ i ∈ s, ∀ x ∈ a, |baseline i x| ≤ 2^(2*L*k))
    (hBudget : overhead L b ell eSlope + 1 < 3*M) :
    (cleared s a d slopeNum (fun i x => moment i x * derivative i x * baseline i x)) * 2 ∈
      Set.Ioc (-(2:ℤ)^(10*M)) ((2:ℤ)^(10*M)) := by
  classical
  let C : I → A → ℤ := fun i x =>
    slopeNum i * (moment i x * derivative i x * baseline i x) * ∏ j ∈ s.erase i, d j
  let E := eSlope + ((b+1)*ell + (2*L+1) + 2*L*k) + L*((b+1)*ell)
  have hcard : (s ×ˢ a).card ≤ 2^(ell+M) := by
    rw [Finset.card_product, pow_add]
    exact Nat.mul_le_mul (hs.trans hL) ha
  have hC (i : I) (hi : i ∈ s) (x : A) (hx : x ∈ a) : |C i x| ≤ 2^E := by
    have den :
        |∏ j ∈ s.erase i, d j| ≤ (2:ℤ)^(L*((b+1)*ell)) := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _j ∈ s.erase i, (2:ℤ)^((b+1)*ell) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j hj => hd j (Finset.mem_of_mem_erase hj))
        _ = (2:ℤ)^((s.erase i).card*((b+1)*ell)) := by
          rw [Finset.prod_const, ← pow_mul, Nat.mul_comm ((b+1)*ell)]
        _ ≤ _ := pow_le_pow_right₀ (by decide)
          (Nat.mul_le_mul_right _ ((Finset.card_erase_le).trans hs))
    dsimp [C, E]
    simp only [abs_mul, pow_add]
    exact mul_le_mul (mul_le_mul (hS i hi)
      (mul_le_mul (mul_le_mul (hMoment i hi x hx) (hDeriv i hi x hx)
        (abs_nonneg _) (by positivity)) (hBase i hi x hx)
        (abs_nonneg _) (by positivity))
      (by positivity) (by positivity)) den (abs_nonneg _) (by positivity)
  have hE : E + (ell+M) + 1 < 10*M := by
    unfold overhead at hBudget
    dsimp [E]
    rw [Nat.mul_assoc]
    omega
  have hsum :=
    CoefficientClearing.centered_after_sum (10*M) E (ell+M) (s ×ˢ a)
      (fun ix => C ix.1 ix.2) hcard (fun ix hix => by
        obtain ⟨hi,hx⟩ := Finset.mem_product.mp hix
        exact hC ix.1 hi ix.2 hx) hE
  rw [Finset.sum_product] at hsum
  exact hsum

/-- There are sufficiently many printed probe lifts for the 10M-bit budget
whenever the actual layout side length is at least six. -/
theorem printed_probe_count (M L : ℕ) (h : 6 ≤ L) :
    10*M+1 ≤ M*(2*L-1)+1 := by
  have hL : 10 ≤ 2*L-1 := by omega
  have hm := Nat.mul_le_mul_left M hL
  omega

/-- At the extreme node t=L−1, each eligible row uses an odd positive
denominator root, and its magnitude is at most 2L. -/
theorem outer_denominator (L x τ : ℕ) (hL : 3 ≤ L) (hx : x < L) (ht : τ < 2)
    (hEven : L % 2 = 0) (hcross : x % 2 = τ % 2) :
    let d : ℤ := (L:ℤ) - 1 - τ + x
    0 < d ∧ d ≤ (2:ℤ)*L ∧ Odd d := by
  dsimp only
  refine ⟨by omega, by omega, ?_⟩
  refine ⟨((L:ℤ) - 2 - τ + x)/2, ?_⟩
  omega

/-- The actual numerator slope `c * α * 2^b` at i=0, with α=2L. -/
theorem outer_slope (L b ell : ℕ) (c : ℤ)
    (hL : L ≤ 2^ell) (hc : |c| ≤ 2^(2*L)) :
    |c * (2*(L:ℤ)) * 2^b| ≤ (2:ℤ)^(2*L+ell+1+b) := by
  have h : (L:ℤ) ≤ (2:ℤ)^ell := by exact_mod_cast hL
  have h' : (2:ℤ)*(L:ℤ) ≤ (2:ℤ)^ell*2 := by linarith
  have ha : |(2:ℤ)*(L:ℤ)| = (2:ℤ)*(L:ℤ) := abs_of_nonneg (by positivity)
  rw [abs_mul, abs_mul, ha, abs_of_nonneg (by positivity : (0:ℤ) ≤ 2^b)]
  simp only [pow_add, pow_one]
  exact mul_le_mul_of_nonneg_right
    (by have := mul_le_mul hc h' (by positivity) (by positivity); linarith)
    (by positivity)

theorem twice_le_pow (L : ℕ) (h : 2 ≤ L) :
    2*L ≤ 2^L := by
  induction L with
  | zero => omega
  | succ L ih =>
    by_cases hL : 2 ≤ L
    · have hh := ih hL
      rw [pow_succ]
      omega
    · have : L = 1 := by omega
      subst L
      decide

/-- No asymptotic notation is required for this sufficient budget. Taking
ell=L trades some slack for the elementary condition L^3 ≤ M. -/
theorem outer_overhead (L b M : ℕ) (hL : 3 ≤ L) (hb : b < L) (hM : L^3 ≤ M) :
    overhead L b L (2*L+L+1+b)+1 < 3*M := by
  have h1 : (b+1)*L ≤ L^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (by omega)
  have h2 : L*((b+1)*L) ≤ L^3 := by
    have e : L^3 = L * L^2 := by ring
    rw [e]
    exact Nat.mul_le_mul_left _ h1
  have h3 : 3*L ≤ L^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ hL
  have h4 : 3*L^2 ≤ L^3 := by
    have e : L^3 = L * L^2 := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ hL
  have h5 : 7*L + 3 ≤ 8*L := by omega
  unfold overhead
  omega

/-- J9 specialization at the literal source denominator and slope. Its
nontrivial layout inputs are exposed as finite cardinality and factor
bounds; this does not assume a bound on the signed answer. -/
theorem outer_centered (s aRows : Finset I) (a : Finset A)
    (rowIndex : I → ℕ) (τ : ℕ) (c : ℤ)
    (moment derivative baseline : I → A → ℤ) (L b M k : ℕ)
    (hL : 3 ≤ L) (hEven : L % 2 = 0) (hτ : τ < 2) (hb : b < L) (hM : L^3 ≤ M)
    (hs : s.card ≤ L) (ha : a.card ≤ 2^M) (hk : L*k ≤ 3*M)
    (hrows : s ⊆ aRows)
    (hx : ∀ i ∈ aRows, rowIndex i < L ∧ rowIndex i % 2 = τ % 2)
    (hc : |c| ≤ 2^(2*L))
    (hMoment : ∀ i ∈ s, ∀ x ∈ a, |moment i x| ≤ 2^((b+1)*L))
    (hDeriv : ∀ i ∈ s, ∀ x ∈ a, |derivative i x| ≤ 2^(2*L+1))
    (hBase : ∀ i ∈ s, ∀ x ∈ a, |baseline i x| ≤ 2^(2*L*k)) :
    let d := fun i => ((L:ℤ)-1-τ+rowIndex i)^(b+1)
    (cleared s a d (fun _ => c*(2*(L:ℤ))*2^b)
      (fun i x => moment i x * derivative i x * baseline i x))*2 ∈
      Set.Ioc (-(2:ℤ)^(10*M)) ((2:ℤ)^(10*M)) := by
  dsimp only
  have hpow := twice_le_pow L (by omega)
  have hpow' : (2:ℤ)*(L:ℤ) ≤ (2:ℤ)^L := by exact_mod_cast hpow
  have hL' : L ≤ 2^L := by omega
  refine centered_10M _ _ _ _ _ _ _ M L b L k (2*L+L+1+b)
    hs hL' ha hk ?_ (fun _ _ => outer_slope L b L c hL' hc)
    hMoment hDeriv hBase (outer_overhead L b M hL hb hM)
  intro i hi
  have ⟨hi0, hi1⟩ := hx i (hrows hi)
  have ⟨hp, hd, _⟩ := outer_denominator L (rowIndex i) τ hL hi0 hτ hEven hi1
  have h' : (L:ℤ)-1-τ+rowIndex i ≤ (2:ℤ)^L := hd.trans hpow'
  rw [abs_pow, abs_of_pos hp, Nat.mul_comm (b+1) L, pow_mul]
  exact pow_le_pow_left₀ hp.le h' _

#print axioms twice_le_pow
#print axioms outer_overhead
#print axioms outer_centered
#print axioms outer_denominator
#print axioms outer_slope
#print axioms cleared_correct
#print axioms centered_10M
#print axioms printed_probe_count

end CompletedPrecisionBudget