import J7FullWordLaw

/-! # Attach exact full labels to the actual physical J7 wires -/

open scoped BigOperators Classical
open J7SourceLabels J7SourceConditioning J7FullWordLaw NativeLabelLaw

namespace J7FullWordCells
noncomputable section
set_option maxHeartbeats 500000

local instance (priority := 100000) {X : Type*} : DecidableEq X :=
  fun _ _ => Classical.propDecidable _

abbrev Slot := Fin 2 × Fin 3
abbrev Tail (R : Type*) := Slot → R
abbrev Word (A R : Type*) := A × R
abbrev Seed (A R : Type*) := Chosen A × Tail R

variable {A R Pair Row Col W : Type*}
variable [Fintype A] [Fintype R] [Nonempty R] [Fintype Pair] [Fintype Row] [Fintype Col]

abbrev B (Pair Row Col : Type*) := Block Pair Row Col
abbrev State (A R Pair Row Col : Type*) := B Pair Row Col → Seed A R

/-- Distinct slots are precisely the private old-pin, subdivision and clone
tail words; ordinary vertices use one slot of their own block. -/
def tailPorts (row : W → Row) (col : W → OrdinaryColumn Pair Col) :
    Wire Pair W → (Block Pair Row Col × Slot) × (Block Pair Row Col × Slot)
  | Sum.inl ((p,side),k) =>
      ((Sum.inl p, (side,1)), (Sum.inl p, (side, if k then 2 else 0)))
  | Sum.inr w =>
      ((Sum.inr (Sum.inl (row w)), (0,0)),
        match col w with
        | Sum.inl (p,side) => (Sum.inl p, (side,2))
        | Sum.inr c => (Sum.inr (Sum.inr c), (0,0)))

omit [Fintype Pair] [Fintype Row] [Fintype Col] in
theorem tailPorts_distinct (row : W → Row) (col : W → OrdinaryColumn Pair Col) (e : Wire Pair W) :
    (tailPorts row col e).1 ≠ (tailPorts row col e).2 := by
  rcases e with ⟨⟨p,side⟩,k⟩ | w
  · intro he
    have hv := congrArg (fun z : Block Pair Row Col × Slot => z.2.2.val) he
    cases k with
    | false =>
      simp only [tailPorts, Bool.false_eq_true, if_false] at hv
      change (1 : ℕ) = 0 at hv
      exact Nat.succ_ne_zero 0 hv
    | true =>
      simp only [tailPorts, if_true] at hv
      change (1 : ℕ) = 2 at hv
      exact Nat.succ_ne_zero 0 (Nat.succ.inj hv).symm
  · intro he
    have hb := congrArg Prod.fst he
    cases h : col w with
    | inl p =>
      obtain ⟨p,s⟩ := p
      simp only [tailPorts, h] at hb
      cases hb
    | inr c =>
      simp only [tailPorts, h] at hb
      cases Sum.inr.inj hb

omit [Fintype Pair] [Fintype Row] [Fintype Col] in
theorem tailPorts_support (row : W → Row) (col : W → OrdinaryColumn Pair Col) (e : Wire Pair W) :
    (tailPorts row col e).1.1 ∈ blockSupport row col e ∧
      (tailPorts row col e).2.1 ∈ blockSupport row col e := by
  rcases e with ⟨⟨p,side⟩,k⟩ | w
  · simp [tailPorts]
  · cases h : col w with
    | inl p => obtain ⟨p,s⟩ := p; simp [tailPorts, h, columnBlock]
    | inr c => simp [tailPorts, h, columnBlock]

def chosenCell (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : Block Pair Row Col → Chosen A) : Wire Pair W → A × A
  | .inl ((p,side),k) =>
    let t := z (.inl p)
    ((gadget t side).1, if k then (gadget t side).2 else t.1)
  | .inr w =>
    ((z (.inr (.inl (row w)))).1,
      match col w with
      | .inl (p,side) => (gadget (z (.inl p)) side).2
      | .inr c => (z (.inr (.inr c))).1)

def toDraw [AddCommGroup A] (z : Chosen A) : Draw A :=
  ⟨z.1, fun s => (gadget z s).1 - z.1, fun s => (gadget z s).2 - (gadget z s).1⟩

omit [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] in
/-- This is exactly the offset model of round 3 on the distinguished
coordinate; differences here are a change of variables, not new draws. -/
theorem chosenCell_eq_cell [AddCommGroup A] (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : Block Pair Row Col → Chosen A) (e : Wire Pair W) :
    chosenCell row col z e = cell row col (fun b => toDraw (z b)) e := by
  rcases e with ⟨⟨p,side⟩,k⟩ | w
  · cases k <;> simp [chosenCell, cell, toDraw, add_sub_cancel]
  · cases h : col w with
    | inl p => obtain ⟨p,s⟩ := p; simp [chosenCell, cell, toDraw, h, add_sub_cancel]
    | inr c => simp [chosenCell, cell, toDraw, h]

def tailCell (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : Block Pair Row Col → Tail R) (e : Wire Pair W) : R × R :=
  let (x,y) := tailPorts row col e
  (z x.1 x.2, z y.1 y.2)

def fullCell (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (e : Wire Pair W) (z : State A R Pair Row Col) : Word A R × Word A R :=
  let x := chosenCell row col (fun i => (z i).1) e
  let y := tailCell row col (fun i => (z i).2) e
  ((x.1,y.1),(x.2,y.2))

def tWeight (z : Tail R) : ℚ := productWeight (fun _ => uniform R) z

theorem tWeight_normalized : (∑ z : Tail R, tWeight z) = 1 := by
  unfold tWeight
  exact productWeight_normalized (A := fun _ : Slot => R) (fun _ => uniform R)
    (fun _ => uniform_normalized (X := R))

omit [Nonempty R] in
theorem tWeight_nonneg (z : Tail R) : 0 ≤ tWeight z :=
  productWeight_nonneg (A := fun _ : Slot => R) (fun _ => uniform R)
    (fun _ x => uniform_nonneg x) z

def weight (_ : Block Pair Row Col) (z : Seed A R) : ℚ := chosenWeight z.1 * tWeight z.2

omit [Fintype Pair] [Fintype Row] [Fintype Col] in
theorem weight_normalized (h : 2 ≤ Fintype.card A) :
    ∀ i : Block Pair Row Col, ∑ z : Seed A R, weight i z = 1 := by
  intro i
  have hh := expect_product (chosenWeight : Chosen A → ℚ) (tWeight : Tail R → ℚ)
    (fun _ => 1) (fun _ => 1)
  simpa only [expect, one_mul, mul_one, weight, chosen_normalized h, tWeight_normalized] using hh

omit [Nonempty R] [Fintype Pair] [Fintype Row] [Fintype Col] in
theorem weight_nonneg (h : 2 ≤ Fintype.card A) (i : Block Pair Row Col) (z : Seed A R) :
    0 ≤ weight i z :=
  mul_nonneg (chosenWeight_nonneg h _) (tWeight_nonneg _)

theorem tail_symbol (i : Slot) (x : R) :
    expect tWeight (fun t => indicator (t i) x) = uniform R x := by
  unfold tWeight
  exact (average_eval (fun _ : Slot => uniform R) (fun _ => uniform_normalized) i
    (fun t => indicator t x)).trans (expect_indicator _ _)

theorem tail_pair (ref : R) {i j : Block Pair Row Col × Slot} (hij : i ≠ j) (x y : R) :
    average (fun _ : Block Pair Row Col => tWeight)
      (fun z => indicator (z i.1 i.2,z j.1 j.2) (x,y)) = uniform R x * uniform R y := by
  simp only [indicator_prod]
  by_cases h : i.1 = j.1
  · rcases i with ⟨b,i⟩
    rcases j with ⟨c,j⟩
    change b = c at h
    subst c
    have hslot : i ≠ j := fun h => hij (by rw [h])
    change average (fun _ : Block Pair Row Col => tWeight)
      (fun z => indicator (z b i) x * indicator (z b j) y) = _
    rw [average_eval (fun _ : Block Pair Row Col => tWeight) (fun _ => tWeight_normalized) b
      (fun t => indicator (t i) x * indicator (t j) y)]
    unfold tWeight
    exact (average_distinct (fun _ => uniform R) (fun _ => uniform_normalized)
      (fun _ => ref) hslot (fun s => indicator s x) (fun t => indicator t y)).trans
        (by rw [expect_indicator, expect_indicator])
  · rw [average_distinct (fun _ : Block Pair Row Col => tWeight) (fun _ => tWeight_normalized)
      (fun _ _ => ref) h (fun z => indicator (z i.2) x) (fun z => indicator (z j.2) y),
      tail_symbol, tail_symbol]

def chosenMean (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (e : Wire Pair W) (c : A × A) : ℚ :=
  average (fun _ : Block Pair Row Col => chosenWeight) (fun z => indicator (chosenCell row col z e) c)

theorem chosenMean_pin (h : 2 ≤ Fintype.card A) (row : W → Row)
    (col : W → OrdinaryColumn Pair Col) (p : Pin Pair) (c : A × A) :
    chosenMean row col (.inl (p,false)) c = pinPair c.1 c.2 := by
  rcases p with ⟨p,s⟩
  rcases c with ⟨a,b⟩
  unfold chosenMean
  simp only [chosenCell, Bool.false_eq_true, if_false]
  convert (average_eval (fun _ : Block Pair Row Col => chosenWeight) (fun _ => chosen_normalized h)
    (.inl p) (fun z => indicator ((gadget z s).1,z.1) (a,b))).trans (chosen_pin_law h s a b) using 1

theorem chosenMean_mate (h : 2 ≤ Fintype.card A) (row : W → Row)
    (col : W → OrdinaryColumn Pair Col) (p : Pin Pair) (c : A × A) :
    chosenMean row col (.inl (p,true)) c = uniform A c.1 * cloneKernel c.1 c.2 := by
  rcases p with ⟨p,s⟩
  rcases c with ⟨a,b⟩
  unfold chosenMean
  simp only [chosenCell, if_true]
  convert (average_eval (fun _ : Block Pair Row Col => chosenWeight) (fun _ => chosen_normalized h)
    (.inl p) (fun z => indicator (gadget z s) (a,b))).trans (chosen_mate_law h s a b) using 1

theorem chosenMean_regular (h : 2 ≤ Fintype.card A) (ref : Chosen A) (row : W → Row)
    (col : W → OrdinaryColumn Pair Col) (w : W) (c : A × A) :
    chosenMean row col (.inr w) c = uniform A c.1 * uniform A c.2 := by
  rcases c with ⟨a,b⟩
  unfold chosenMean
  cases hc : col w with
  | inl p =>
    obtain ⟨p,s⟩ := p
    simp only [chosenCell, hc, indicator_prod]
    rw [average_distinct (fun _ : Block Pair Row Col => chosenWeight)
      (fun _ => chosen_normalized h) (fun _ => ref) (by simp)
      (fun z => indicator z.1 a) (fun z => indicator (gadget z s).2 b),
      chosen_old_uniform h, chosen_clone_uniform h]
  | inr v =>
    simp only [chosenCell, hc, indicator_prod]
    rw [average_distinct (fun _ : Block Pair Row Col => chosenWeight)
      (fun _ => chosen_normalized h) (fun _ => ref) (by simp)
      (fun z => indicator z.1 a) (fun z => indicator z.1 b),
      chosen_old_uniform h, chosen_old_uniform h]

theorem full_marginal (ref : R) (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (e : Wire Pair W) (c : Word A R × Word A R) :
    meanCell (productWeight (weight (A:=A) (R:=R))) (fullCell row col) e c =
      chosenMean row col e (c.1.1,c.2.1) * (uniform R c.1.2 * uniform R c.2.2) := by
  rcases c with ⟨⟨c₁,c₂⟩,⟨c₃,c₄⟩⟩
  have hi : ∀ (x : A × A) (y : R × R),
      indicator ((x.1,y.1),(x.2,y.2)) ((c₁,c₂),(c₃,c₄)) =
        indicator x (c₁,c₃) * indicator y (c₂,c₄) := by
    rintro ⟨a,b⟩ ⟨d,e⟩
    simp only [indicator_prod]
    ac_rfl
  unfold meanCell fullCell
  simp only [hi]
  have hp := average_product (I := Block Pair Row Col) (X := Chosen A) (Y := Tail R)
    (fun _ => chosenWeight) (fun _ => tWeight)
    (fun z => indicator (chosenCell row col z e) (c₁,c₃))
    (fun z => indicator (tailCell row col z e) (c₂,c₄))
  unfold average at hp
  unfold weight
  rw [hp]
  unfold chosenMean tailCell average
  exact congrArg
    (fun k => expect (productWeight (fun _ : Block Pair Row Col => chosenWeight))
      (fun z => indicator (chosenCell row col z e) (c₁,c₃)) * k)
    (tail_pair ref (tailPorts_distinct row col e) c₂ c₄)

#print axioms chosenCell_eq_cell
#print axioms tailPorts_distinct
#print axioms tailPorts_support
#print axioms chosenMean_pin
#print axioms chosenMean_mate
#print axioms chosenMean_regular
#print axioms full_marginal

end
end J7FullWordCells
