import J8J9Grouped
import J9EndFactors

/-! Exact finite grouping plus a pointwise-to-centered precision argument.
The finite assignment cube is a dependent product, so the bit budget never
counts repeated assignments introduced by grouping. -/

namespace J8J9Grouped
open scoped BigOperators Classical
noncomputable section

variable {G I : Type*} [Fintype G] [DecidableEq G] [DecidableEq I]
variable {Ω : G → Type*} [∀ g, Fintype (Ω g)]

def insertSpecial {K : Type*}
    (u : (g : G) → Ω g → K) (s t : G) (v : Ω s → K) (w : Ω t → K)
    (g : G) (x : Ω g) : K :=
  if hs : g = s then v (hs ▸ x) else if ht : g = t then w (ht ▸ x) else u g x

theorem splitSpecial {K : Type*} [CommSemiring K]
    (u : (g : G) → Ω g → K) (s t : G) (h : s ≠ t) (v : Ω s → K) (w : Ω t → K) :
    (∑ x : (g : G) → Ω g, ∏ g : G, insertSpecial u s t v w g (x g)) =
      (∑ x : Ω s, v x) * (∑ x : Ω t, w x) *
        ∏ g ∈ ((Finset.univ : Finset G).erase s).erase t, ∑ x : Ω g, u g x := by
  rw [← Fintype.prod_sum]
  have he : ∀ g : G, (∑ x : Ω g, insertSpecial u s t v w g x) =
    if g = s then ∑ x : Ω s, v x else if g = t then ∑ x : Ω t, w x else ∑ x : Ω g, u g x := by
    intro g
    by_cases hs : g = s
    · subst g; simp [insertSpecial]
    · by_cases ht : g = t
      · subst g; simp [insertSpecial, hs]
      · simp [insertSpecial, hs, ht]
  simp only [he]
  exact J9End.product_two_marked (fun g => ∑ x : Ω g, u g x) s t h _ _

theorem numerator_as_assignment_sum (s : Finset I) (den : I → ℤ) (scale : ℤ)
    (u : (g : G) → Ω g → ℤ) (gs gt : G) (off : gs ≠ gt)
    (v : Ω gs → ℤ) (w : I → Ω gt → ℤ) :
    numerator s den scale (∏ g ∈ ((Finset.univ : Finset G).erase gs).erase gt,
      ∑ x : Ω g, u g x) (∑ x : Ω gs, v x) (fun i => ∑ x : Ω gt, w i x) =
    CompletedPrecisionBudget.cleared s Finset.univ den (fun _ => scale)
      (fun i (x : (g : G) → Ω g) => ∏ g : G, insertSpecial u gs gt v (w i) g (x g)) := by
  unfold numerator CompletedPrecisionBudget.cleared
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul, ← Finset.mul_sum, splitSpecial u gs gt off]
  ring

omit [Fintype G] [DecidableEq G] [∀ g, Fintype (Ω g)] in
theorem assignment_term_majorant (s : Finset I)
    (rowIndex : I → ℕ) (τ : ℕ) (c : ℤ)
    (term : I → ((g : G) → Ω g) → ℤ) (L b M k : ℕ)
    [Fintype ((g : G) → Ω g)]
    (hL : 3 ≤ L) (even : L % 2 = 0) (hτ : τ < 2) (hb : b < L) (hM : L^3 ≤ M)
    (hs : s.card ≤ L) (ha : Fintype.card ((g : G) → Ω g) ≤ 2^M) (hk : L*k ≤ 3*M)
    (hx : ∀ i ∈ s, rowIndex i < L ∧ rowIndex i % 2 = τ % 2)
    (hc : |c| ≤ 2^(2*L))
    (perTerm : ∀ i ∈ s, ∀ x, |term i x| ≤ (2:ℤ)^((b+1)*L+(2*L+1)+2*L*k)) :
    let den := fun i => ((L:ℤ)-1-τ+rowIndex i)^(b+1)
    (CompletedPrecisionBudget.cleared s Finset.univ den (fun _ => c*(2*(L:ℤ))*2^b) term)*2 ∈
      Set.Ioc (-(2:ℤ)^(10*M)) ((2:ℤ)^(10*M)) := by
  dsimp only
  let den := fun i => ((L:ℤ)-1-τ+rowIndex i)^(b+1)
  let E := 2*L+L+1+b + ((b+1)*L+(2*L+1)+2*L*k) + L*((b+1)*L)
  let C : I × ((g : G) → Ω g) → ℤ := fun ix =>
    (c*(2*(L:ℤ))*2^b) * term ix.1 ix.2 * ∏ j ∈ s.erase ix.1, den j
  have hpow := CompletedPrecisionBudget.twice_le_pow L (by omega)
  have hpow' : (2:ℤ)*(L:ℤ) ≤ (2:ℤ)^L := by exact_mod_cast hpow
  have hL' : L ≤ 2^L := by omega
  have hcard : (s ×ˢ (Finset.univ : Finset ((g : G) → Ω g))).card ≤ 2^(L+M) := by
    rw [Finset.card_product, pow_add, Finset.card_univ]
    exact Nat.mul_le_mul (hs.trans hL') ha
  have hden (i : I) (hi : i ∈ s) : |den i| ≤ (2:ℤ)^((b+1)*L) := by
    have ⟨hi0, hi1⟩ := hx i hi
    have ⟨hp, hu, _⟩ := CompletedPrecisionBudget.outer_denominator L (rowIndex i) τ hL hi0 hτ even hi1
    dsimp [den]
    rw [abs_pow, abs_of_pos hp, Nat.mul_comm (b+1) L, pow_mul]
    exact pow_le_pow_left₀ hp.le (hu.trans hpow') _
  have hC (ix : I × ((g : G) → Ω g))
      (hi : ix ∈ s ×ˢ (Finset.univ : Finset ((g : G) → Ω g))) : |C ix| ≤ 2^E := by
    have denprod :
        |∏ j ∈ s.erase ix.1, den j| ≤ (2:ℤ)^(L*((b+1)*L)) := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _j ∈ s.erase ix.1, (2:ℤ)^((b+1)*L) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _)
            (fun j hj => hden j (Finset.mem_of_mem_erase hj))
        _ = (2:ℤ)^((s.erase ix.1).card*((b+1)*L)) := by
          rw [Finset.prod_const, ← pow_mul, Nat.mul_comm ((b+1)*L)]
        _ ≤ _ := pow_le_pow_right₀ (by decide)
          (Nat.mul_le_mul_right _ ((Finset.card_erase_le).trans hs))
    have ht := perTerm ix.1 (Finset.mem_product.mp hi).1 ix.2
    have hS := CompletedPrecisionBudget.outer_slope L b L c hL' hc
    dsimp [C,E]
    rw [abs_mul, abs_mul, pow_add, pow_add (2:ℤ) (2*L+L+1+b)]
    exact mul_le_mul (mul_le_mul hS ht (abs_nonneg _) (by positivity)) denprod
      (abs_nonneg _) (by positivity)
  have hE : E + (L+M) + 1 < 10*M := by
    have B := CompletedPrecisionBudget.outer_overhead L b M hL hb hM
    unfold CompletedPrecisionBudget.overhead at B
    dsimp [E]
    rw [Nat.mul_assoc]
    omega
  have hr := CoefficientClearing.centered_after_sum (10*M) E (L+M)
    (s ×ˢ (Finset.univ : Finset ((g : G) → Ω g))) C hcard hC hE
  rw [Finset.sum_product] at hr
  exact hr

#print axioms splitSpecial
#print axioms numerator_as_assignment_sum
#print axioms assignment_term_majorant
end
end J8J9Grouped
