import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-!
# Physical input to the v9 J7 label construction

An exterior edge indexes two original unary pins. Each such pin has a
private subdivision row and a private clone equality column. The row owns
exactly the pin and private-clone wires. Any remaining wire is an ordinary
subdivision row to an ordinary column or to a private clone. The latter
attachments are bounded by the two remaining ports of a trivalent column.

The theorems below count the actual primitive blocks read by ordered pairs
of wires. They do not presume independence of two labels attached to one
pin gadget or to two pins of the same exterior edge.
-/

open scoped BigOperators Classical

namespace J7SourceLabels

noncomputable section

abbrev Pin (Pair : Type*) := Pair × Fin 2

/-- First sum type: one of the two labelled wires owned by a private
subdivision. Second sum type: all other physical wires. -/
abbrev Wire (Pair W : Type*) := (Pin Pair × Bool) ⊕ W

/-- Each exterior pair supplies a shared draw plus its two private offsets;
each ordinary vertex supplies a separate draw. -/
abbrev Block (Pair Row Col : Type*) := Pair ⊕ (Row ⊕ Col)

/-- A regular wire's old endpoint: private clone or ordinary column. -/
abbrev OrdinaryColumn (Pair Col : Type*) := Pin Pair ⊕ Col

def columnBlock {Pair Row Col : Type*} : OrdinaryColumn Pair Col → Block Pair Row Col
  | .inl p => .inl p.1
  | .inr y => .inr (.inr y)

def blockSupport {Pair Row Col W : Type*}
    (row : W → Row) (col : W → OrdinaryColumn Pair Col) : Wire Pair W → Finset (Block Pair Row Col)
  | .inl (p, _) => {Sum.inl p.1}
  | .inr w => {Sum.inr (Sum.inl (row w)), columnBlock (col w)}

@[simp] theorem support_pin_or_clone {Pair Row Col W : Type*}
    (row : W → Row) (col : W → OrdinaryColumn Pair Col) (p : Pin Pair) (k : Bool) :
    blockSupport row col (Sum.inl (p, k)) = {Sum.inl p.1} := rfl

@[simp] theorem support_ordinary {Pair Row Col W : Type*}
    (row : W → Row) (col : W → OrdinaryColumn Pair Col) (w : W) :
    blockSupport row col (Sum.inr w) = {Sum.inr (Sum.inl (row w)), columnBlock (col w)} := rfl

theorem support_at_most_two {Pair Row Col W : Type*}
    (row : W → Row) (col : W → OrdinaryColumn Pair Col) (e : Wire Pair W) :
    (blockSupport row col e).card ≤ 2 := by
  cases e with
  | inl p => rcases p with ⟨p, k⟩; simp
  | inr w =>
    simp only [support_ordinary]
    exact (Finset.card_insert_le _ _).trans (by simp)

theorem pair_support_at_most_four {Pair Row Col W : Type*}
    (row : W → Row) (col : W → OrdinaryColumn Pair Col) (e f : Wire Pair W) :
    (blockSupport row col e ∪ blockSupport row col f).card ≤ 4 := by
  exact (Finset.card_union_le _ _).trans
    (by have he := support_at_most_two row col e
        have hf := support_at_most_two row col f
        omega)

section ExplicitDraws

variable {A Pair Row Col W : Type*} [AddCommGroup A]

/-- The block for one exterior pair comprises its shared pin label and
two offset pairs. Ordinary vertices each read one separate label. Unused
coordinates of a block-value tuple do not enter any endpoint label. -/
structure Draw (A : Type*) where
  label : A
  avoidOffset : Fin 2 → A
  cloneOffset : Fin 2 → A

def drawEquiv (A : Type*) : (A × (Fin 2 → A) × (Fin 2 → A)) ≃ Draw A where
  toFun x := ⟨x.1, x.2.1, x.2.2⟩
  invFun x := (x.label, x.avoidOffset, x.cloneOffset)
  left_inv := by rintro ⟨a, d, e⟩; rfl
  right_inv := by rintro ⟨a, d, e⟩; rfl

instance [Fintype A] : Fintype (Draw A) := Fintype.ofEquiv _ (drawEquiv A)

def cell (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (v : Block Pair Row Col → Draw A) : Wire Pair W → A × A
  | .inl ((pair, side), kind) =>
    let draw := v (Sum.inl pair)
    let s := draw.label + draw.avoidOffset side
    (s, if kind then s + draw.cloneOffset side else draw.label)
  | .inr w =>
    ( (v (Sum.inr (Sum.inl (row w)))).label,
      match col w with
      | .inl p =>
        let draw := v (Sum.inl p.1)
        draw.label + draw.avoidOffset p.2 + draw.cloneOffset p.2
      | .inr c => (v (Sum.inr (Sum.inr c))).label )

/-- This is a source-derived local dependence certificate, not an abstract
independence assertion between wire ends. -/
theorem cell_depends_on_support (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (v v' : Block Pair Row Col → Draw A) (e : Wire Pair W)
    (h : ∀ b ∈ blockSupport row col e, v b = v' b) :
    cell row col v e = cell row col v' e := by
  cases e with
  | inl p =>
    rcases p with ⟨⟨a, side⟩, k⟩
    have h' := h (Sum.inl a) (by simp)
    simp [cell, h']
  | inr w =>
    have hr := h (Sum.inr (Sum.inl (row w))) (by simp)
    have hc := h (columnBlock (col w)) (by simp)
    cases hw : col w <;> simp [cell, hw, hr, columnBlock] at hc ⊢ <;> rw [hc]

/-- Both pins of an exterior pair use exactly the shared block label,
independent of any Boolean sign or private offset. -/
theorem pin_tie (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (v : Block Pair Row Col → Draw A) (p : Pair) (side side' : Fin 2) :
    (cell row col v (Sum.inl ((p, side), false))).2 =
      (cell row col v (Sum.inl ((p, side'), false))).2 := rfl

theorem pin_is_off_diagonal (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (v : Block Pair Row Col → Draw A) (p : Pair) (side : Fin 2)
    (h : (v (Sum.inl p)).avoidOffset side ≠ 0) :
    (cell row col v (Sum.inl ((p, side), false))).1 ≠
      (cell row col v (Sum.inl ((p, side), false))).2 := by
  change (v (Sum.inl p)).label + (v (Sum.inl p)).avoidOffset side ≠ (v (Sum.inl p)).label
  intro he
  apply h
  exact add_left_cancel (he.trans (add_zero _).symm)

end ExplicitDraws

section Incidences

variable {Pair Row Col W : Type*} [Fintype Pair] [Fintype W]

def touched (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (b : Block Pair Row Col) : Finset (Wire Pair W) :=
  Finset.univ.filter fun e => b ∈ blockSupport row col e

private theorem card_filter_eq_sum {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ x : X, if p x then (1 : ℕ) else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem sum_special (p : Pair) :
    (∑ z : Pin Pair × Bool, if z.1.1 = p then (1 : ℕ) else 0) = 4 := by
  rw [Fintype.sum_prod_type]
  have h₁ (z : Pin Pair) : (∑ _ : Bool, if z.1 = p then (1 : ℕ) else 0) =
      if z.1 = p then 2 else 0 := by
    by_cases hz : z.1 = p <;> simp [hz]
  simp_rw [h₁]
  rw [Fintype.sum_prod_type]
  have h₂ (q : Pair) : (∑ _ : Fin 2, if q = p then (2 : ℕ) else 0) =
      if q = p then 4 else 0 := by
    by_cases hq : q = p <;> simp [hq]
  simp_rw [h₂]
  simp

omit [Fintype Pair] in
private theorem sum_private (col : W → OrdinaryColumn Pair Col) (p : Pair) :
    (∑ w : W, if columnBlock (Row := Row) (col w) = Sum.inl p then (1 : ℕ) else 0) =
      ∑ b : Fin 2, (Finset.univ.filter fun w : W => col w = Sum.inl (p,b)).card := by
  simp only [card_filter_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  cases h : col w with
  | inl x =>
    rcases x with ⟨q, b⟩
    by_cases he : q = p
    · subst q
      simp [columnBlock, Sum.inl.injEq, Prod.mk.injEq]
    · simp [columnBlock, Sum.inl.injEq, Prod.mk.injEq, he]
  | inr a => simp [columnBlock]

/-- Source degree two on ordinary subdivisions, degree three on the old
columns. A clone already uses a private wire, so it has at most two
ordinary wires. These actual incidence caps imply eight touching wires for
an exterior-pair block, two for a regular row block and three for an old
column block. -/
theorem touching_counts (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_cap : ∀ r, (Finset.univ.filter fun w : W => row w = r).card ≤ 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3) :
    (∀ p : Pair, (touched row col (Sum.inl p)).card ≤ 8) ∧
    (∀ r : Row, (touched row col (Sum.inr (Sum.inl r))).card ≤ 2) ∧
    (∀ c : Col, (touched row col (Sum.inr (Sum.inr c))).card ≤ 3) := by
  constructor
  · intro p
    unfold touched
    rw [card_filter_eq_sum, Fintype.sum_sum_type]
    have hps (z : Pin Pair × Bool) :
        Sum.inl p ∈ blockSupport row col (Sum.inl z) ↔ z.1.1 = p := by
      rcases z with ⟨i,k⟩
      simp [eq_comm]
    have hws (w : W) :
        Sum.inl p ∈ blockSupport row col (Sum.inr w) ↔
          Sum.inl p = columnBlock (Row := Row) (col w) := by simp
    simp_rw [hps, hws, sum_special]
    have hreg : (∑ w : W, if Sum.inl p = columnBlock (Row := Row) (col w) then (1 : ℕ) else 0) =
        ∑ b : Fin 2, (Finset.univ.filter fun w : W => col w = Sum.inl (p,b)).card := by
      simpa only [eq_comm] using (sum_private (Row := Row) col p)
    rw [hreg]
    have hc := Finset.sum_le_sum fun b (_ : b ∈ (Finset.univ : Finset (Fin 2))) =>
      clone_cap (p,b)
    have hc' : (∑ b : Fin 2, (Finset.univ.filter fun w : W => col w = Sum.inl (p,b)).card) ≤ 4 := by
      simpa using hc
    omega
  · constructor
    · intro r
      have hc (w : W) : Sum.inr (Sum.inl r) ≠ columnBlock (Row := Row) (col w) := by
        cases col w <;> simp [columnBlock]
      unfold touched
      rw [card_filter_eq_sum, Fintype.sum_sum_type]
      have hps (z : Pin Pair × Bool) : Sum.inr (Sum.inl r) ∉ blockSupport row col (Sum.inl z) := by
        rcases z with ⟨i,k⟩; simp
      have hws (w : W) :
          Sum.inr (Sum.inl r) ∈ blockSupport row col (Sum.inr w) ↔ row w = r := by simp [hc, eq_comm]
      simp_rw [hps, if_false, Finset.sum_const_zero, zero_add, hws, ← card_filter_eq_sum]
      exact row_cap r
    · intro c
      have hc (w : W) : Sum.inr (Sum.inr c) = columnBlock (Row := Row) (col w) ↔ col w = Sum.inr c := by
        cases col w <;> simp [columnBlock, eq_comm]
      unfold touched
      rw [card_filter_eq_sum, Fintype.sum_sum_type]
      have hps (z : Pin Pair × Bool) : Sum.inr (Sum.inr c) ∉ blockSupport row col (Sum.inl z) := by
        rcases z with ⟨i,k⟩; simp
      have hws (w : W) :
          Sum.inr (Sum.inr c) ∈ blockSupport row col (Sum.inr w) ↔ col w = Sum.inr c := by simp [hc]
      simp_rw [hps, if_false, Finset.sum_const_zero, zero_add, hws, ← card_filter_eq_sum]
      exact col_cap c

def dependentOn (row : W → Row) (col : W → OrdinaryColumn Pair Col) (e : Wire Pair W) :
    Finset (Wire Pair W) :=
  (blockSupport row col e).biUnion (touched row col)

theorem mem_dependentOn (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (e f : Wire Pair W) :
    f ∈ dependentOn row col e ↔ ∃ b ∈ blockSupport row col e, b ∈ blockSupport row col f := by
  simp [dependentOn, touched]

/-- Exact finite replacement for the statement "only O(M) ordered
wire pairs depend on a common block." Self-pairs are included. -/
theorem ordered_dependent_pairs_le16 (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_cap : ∀ r, (Finset.univ.filter fun w : W => row w = r).card ≤ 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3) :
    (∑ e : Wire Pair W, (dependentOn row col e).card) ≤ 16 * Fintype.card (Wire Pair W) := by
  obtain ⟨hc₁, hc₂, hc₃⟩ := touching_counts row col row_cap clone_cap col_cap
  have hc (b : Block Pair Row Col) : (touched row col b).card ≤ 8 := by
    cases b with
    | inl p => exact hc₁ p
    | inr r =>
      cases r with
      | inl r => exact (hc₂ r).trans (by decide)
      | inr c => exact (hc₃ c).trans (by decide)
  have hd (e : Wire Pair W) : (dependentOn row col e).card ≤ 16 := by
    calc
      _ ≤ ∑ b ∈ blockSupport row col e, (touched row col b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ blockSupport row col e, (8 : ℕ) := Finset.sum_le_sum fun b _ => hc b
      _ ≤ 16 := by
        simpa only [Finset.sum_const, nsmul_eq_mul] using
          Nat.mul_le_mul_right 8 (support_at_most_two row col e)
  have hs := Finset.sum_le_sum fun e (_ : e ∈ (Finset.univ : Finset (Wire Pair W))) => hd e
  simpa [Nat.mul_comm] using hs

end Incidences

#print axioms pair_support_at_most_four
#print axioms cell_depends_on_support
#print axioms pin_tie
#print axioms pin_is_off_diagonal
#print axioms touching_counts
#print axioms ordered_dependent_pairs_le16

end
end J7SourceLabels
