import J7SourceAssembly
import NativeLabelLaw

/-! # J7 source full words: exact product and gadget marginals -/

open scoped BigOperators Classical
open J7SourceConditioning

namespace J7FullWordLaw
noncomputable section
set_option maxHeartbeats 2000000

def uniform (X : Type*) [Fintype X] (_ : X) : ℚ := 1 / Fintype.card X

theorem uniform_nonneg {X : Type*} [Fintype X] (x : X) : 0 ≤ uniform X x := by
  unfold uniform
  positivity

theorem uniform_normalized {X : Type*} [Fintype X] [Nonempty X] :
    (∑ x : X, uniform X x) = 1 := by
  simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

theorem expect_indicator {X : Type*} [Fintype X] (w : X → ℚ) (x : X) :
    expect w (fun z => indicator z x) = w x := by
  unfold expect indicator
  simp

theorem average_eval {I X : Type*} [Fintype I] [Fintype X]
    (w : I → X → ℚ) (h : ∀ i, ∑ x, w i x = 1) (i : I) (f : X → ℚ) :
    average w (fun z => f (z i)) = expect (w i) f := by
  unfold average expect productWeight
  calc
    _ = ∑ z : I → X, ∏ j : I, w j (z j) * (if j = i then f (z j) else 1) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.prod_mul_distrib]
      have hp : (∏ j : I, if j = i then f (z j) else 1) = f (z i) := by
        refine (Finset.prod_eq_single i (fun j _ hj => if_neg hj)
          (fun hi => (hi (Finset.mem_univ i)).elim)).trans (if_pos rfl)
      rw [hp]
    _ = ∏ j : I, ∑ x : X, w j x * (if j = i then f x else 1) := by
      rw [Fintype.prod_sum]
    _ = _ := by
      refine Finset.prod_eq_single i (fun j _ hj => ?_) (fun hi => (hi (Finset.mem_univ i)).elim) |>.trans ?_
      · simp [hj, h j]
      · simp

theorem average_distinct {I X : Type*} [Fintype I] [Fintype X]
    (w : I → X → ℚ) (norm : ∀ i, ∑ x, w i x = 1) (ref : I → X)
    {i j : I} (hne : i ≠ j) (f g : X → ℚ) :
    average w (fun z => f (z i) * g (z j)) = expect (w i) f * expect (w j) g := by
  have h := expectation_disjoint_supports w norm (fun k => k = i) (fun k => k = j)
    (fun k hi hj => hne (hi.symm.trans hj)) ref (fun z => f (z i)) (fun z => g (z j))
    (fun x y hxy => congrArg f (hxy i rfl)) (fun x y hxy => congrArg g (hxy j rfl))
  rw [h, average_eval w norm i f, average_eval w norm j g]

theorem expect_product {X Y : Type*} [Fintype X] [Fintype Y]
    (w : X → ℚ) (v : Y → ℚ) (f : X → ℚ) (g : Y → ℚ) :
    expect (fun z : X × Y => w z.1 * v z.2) (fun z => f z.1 * g z.2) =
      expect w f * expect v g := by
  unfold expect
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  dsimp only
  ring

theorem average_product {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
    (w : I → X → ℚ) (v : I → Y → ℚ) (f : (I → X) → ℚ) (g : (I → Y) → ℚ) :
    average (fun i (z : X × Y) => w i z.1 * v i z.2)
      (fun z => f (fun i => (z i).1) * g (fun i => (z i).2)) =
      average w f * average v g := by
  unfold average
  rw [← expect_product (productWeight w) (productWeight v)]
  unfold expect
  let e : (I → X × Y) ≃ (I → X) × (I → Y) :=
    ⟨fun z => (fun i => (z i).1, fun i => (z i).2),
      fun z i => (z.1 i,z.2 i), by intro z; funext i; exact Prod.eta (z i),
      by intro z; cases z; rfl⟩
  refine Fintype.sum_equiv e _ _ (fun z => ?_)
  dsimp [productWeight, e]
  rw [Finset.prod_mul_distrib]

theorem indicator_prod {X Y : Type*} (x x' : X) (y y' : Y) :
    indicator (x,y) (x',y') = indicator x x' * indicator y y' := by
  by_cases ha : x = x' <;> by_cases hb : y = y' <;> simp [indicator, ha, hb]

section Chosen
open NativeLabelLaw
variable {A : Type*} [Fintype A]

/-- Shared first symbol, followed by the row and clone symbols for each
of the two pins. The old pin symbols of other coordinates are not shared. -/
abbrev Chosen (A : Type*) := A × (A × A) × (A × A)

def gadget (z : Chosen A) (s : Fin 2) : A × A :=
  if s = 0 then z.2.1 else z.2.2

def pairLaw (a : A) (x : A × A) : ℚ := rowKernel a x.1 * cloneKernel x.1 x.2

def chosenWeight (z : Chosen A) : ℚ := uniform A z.1 * (pairLaw z.1 z.2.1 * pairLaw z.1 z.2.2)

theorem pairLaw_normalized (h : 2 ≤ Fintype.card A) (a : A) :
    (∑ x : A × A, pairLaw a x) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [pairLaw, ← Finset.mul_sum, cloneKernel_normalized h, mul_one, rowKernel_normalized h]

theorem pairLaw_nonneg (h : 2 ≤ Fintype.card A) (a : A) (x : A × A) :
    0 ≤ pairLaw a x := by
  have hr : (0 : ℚ) < Fintype.card A := by exact_mod_cast (by omega : 0 < Fintype.card A)
  have htwo : (2 : ℚ) ≤ Fintype.card A := by exact_mod_cast h
  unfold pairLaw rowKernel cloneKernel qSize
  split
  · simp
  · split
    · exact mul_nonneg (div_nonneg (by norm_num) (by linarith)) (div_nonneg (by norm_num) hr.le)
    · exact mul_nonneg (div_nonneg (by norm_num) (by linarith))
        (div_nonneg (by linarith) (mul_nonneg hr.le (by linarith)))

theorem chosenWeight_nonneg (h : 2 ≤ Fintype.card A) (z : Chosen A) :
    0 ≤ chosenWeight z :=
  mul_nonneg (uniform_nonneg _) (mul_nonneg (pairLaw_nonneg h _ _) (pairLaw_nonneg h _ _))

theorem chosen_marginal (h : 2 ≤ Fintype.card A) (side : Fin 2)
    (f : A → A → A → ℚ) :
    expect chosenWeight (fun z : Chosen A => f z.1 (gadget z side).1 (gadget z side).2) =
      ∑ a : A, ∑ s : A, ∑ b : A, tripleMass a s b * f a s b := by
  unfold expect
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  by_cases hs : side = 0
  · simp only [gadget, hs, if_true]
    have hstep (x : A × A) :
        (∑ y : A × A, chosenWeight (a,x,y) * f a x.1 x.2) =
          uniform A a * pairLaw a x * f a x.1 x.2 := by
      calc
        _ = (uniform A a * pairLaw a x * f a x.1 x.2) * (∑ y : A × A, pairLaw a y) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by unfold chosenWeight; dsimp only; ring
        _ = _ := by rw [pairLaw_normalized h, mul_one]
    simp only [hstep, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => by
      unfold uniform pairLaw tripleMass pinPair qSize; dsimp only; ring
  · simp only [gadget, hs, if_false]
    rw [Finset.sum_comm]
    have hstep (y : A × A) :
        (∑ x : A × A, chosenWeight (a,x,y) * f a y.1 y.2) =
          uniform A a * pairLaw a y * f a y.1 y.2 := by
      calc
        _ = (uniform A a * pairLaw a y * f a y.1 y.2) * (∑ x : A × A, pairLaw a x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by unfold chosenWeight; dsimp only; ring
        _ = _ := by rw [pairLaw_normalized h, mul_one]
    change (∑ y : A × A, ∑ x : A × A, chosenWeight (a,x,y) * f a y.1 y.2) = _
    simp only [hstep, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => by
      unfold uniform pairLaw tripleMass pinPair qSize; dsimp only; ring

theorem chosen_normalized (h : 2 ≤ Fintype.card A) :
    (∑ z : Chosen A, chosenWeight z) = 1 := by
  have hh := chosen_marginal h (0 : Fin 2) (fun (_ _ _ : A) => 1)
  simpa only [expect, mul_one, tripleMass_normalized h] using hh

theorem chosen_old_uniform (h : 2 ≤ Fintype.card A) (a : A) :
    expect chosenWeight (fun z => indicator z.1 a) = uniform A a := by
  rw [chosen_marginal h 0 (fun b _ _ => indicator b a)]
  simp only [indicator]
  simp [pin_symbol_uniform h, uniform, qSize]

theorem chosen_clone_uniform (h : 2 ≤ Fintype.card A) (side : Fin 2) (b : A) :
    expect chosenWeight (fun z => indicator (gadget z side).2 b) = uniform A b := by
  rw [chosen_marginal h side (fun _ _ c => indicator c b)]
  simp [indicator]
  rw [Finset.sum_comm]
  simpa only [uniform, qSize] using clone_symbol_uniform h b

theorem chosen_pin_law (h : 2 ≤ Fintype.card A) (side : Fin 2) (s a : A) :
    expect chosenWeight (fun z => indicator ((gadget z side).1,z.1) (s,a)) = pinPair s a := by
  rw [chosen_marginal h side (fun x y _ => indicator (y,x) (s,a))]
  simp only [indicator, Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  exact joint_pin_edge h s a

theorem chosen_mate_law (h : 2 ≤ Fintype.card A) (side : Fin 2) (s b : A) :
    expect chosenWeight (fun z => indicator (gadget z side) (s,b)) =
      uniform A s * cloneKernel s b := by
  rw [chosen_marginal h side (fun _ y z => indicator (y,z) (s,b))]
  simp only [indicator, Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  exact joint_clone_edge h s b

end Chosen

#print axioms average_distinct
#print axioms average_product
#print axioms chosen_marginal
#print axioms chosen_normalized
#print axioms chosen_pin_law
#print axioms chosen_mate_law

end
end J7FullWordLaw
