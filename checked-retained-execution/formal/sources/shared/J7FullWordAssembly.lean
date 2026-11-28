import J7FullWordCells

/-! # The actual full J7 wire law feeds supported conditional placement -/

open scoped BigOperators Classical
open J7SourceLabels J7SourceConditioning J7FullWordLaw J7FullWordCells NativeLabelLaw

namespace J7FullWordAssembly
noncomputable section
set_option maxHeartbeats 2500000

local instance (priority := 100000) : DecidableEq Slot :=
  fun _ _ => Classical.propDecidable _

local instance (priority := 100000) {P R C : Type*} : DecidableEq (Block P R C) :=
  fun _ _ => Classical.propDecidable _

variable {A R Pair Row Col W : Type*}
variable [Fintype A] [Fintype R] [Nonempty R]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W]

def denom (A R : Type*) [Fintype A] [Fintype R] : ℚ :=
  (Fintype.card A : ℚ)^2 * (Fintype.card R : ℚ)^2

/-- A tail with t more source coordinates has r^t equally likely words.
A full ordered row/column cell therefore has denominator r^(2(t+1)). -/
theorem denom_coordinates (A : Type*) [Fintype A] (t : ℕ) :
    denom A (Fin t → A) = (Fintype.card A : ℚ)^(2*(t+1)) := by
  unfold denom
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← pow_mul, ← pow_add]
  congr 1
  ring

def pinEmbed (Pair W : Type*) : Pin Pair ↪ Wire Pair W :=
  ⟨fun p => .inl (p,false), by intro _ _ h; exact congrArg Prod.fst (Sum.inl.inj h)⟩

def pinWires (Pair W : Type*) [Fintype Pair] : Finset (Wire Pair W) :=
  Finset.univ.map (pinEmbed Pair W)

abbrev law (A R Pair Row Col : Type*) [Fintype A] [Fintype R]
    [Fintype Pair] [Fintype Row] [Fintype Col] := productWeight (weight (A:=A) (R:=R) (Pair:=Pair) (Row:=Row) (Col:=Col))

omit [Fintype W] in
theorem pin_marginal_sum (h : 2 ≤ Fintype.card A) (ref : R)
    (row : W → Row) (col : W → OrdinaryColumn Pair Col) (c : Word A R × Word A R) :
    (∑ e ∈ pinWires Pair W, meanCell (law A R Pair Row Col) (fullCell row col) e c) =
      if c.1.1 = c.2.1 then 0 else
        ((Fintype.card A : ℚ) / (Fintype.card A - 1)) *
          ((Fintype.card (Pin Pair) : ℚ) / denom A R) := by
  unfold pinWires
  rw [Finset.sum_map]
  simp only [pinEmbed, Function.Embedding.coeFn_mk, full_marginal ref, chosenMean_pin h, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, pinPair_closed]
  by_cases he : c.1.1 = c.2.1
  · simp [he]
  · simp only [he, if_false, uniform, qSize, denom]
    have hr : (0 : ℚ) < Fintype.card A := by exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ 1) h)
    have hr2 : (2 : ℚ) ≤ Fintype.card A := by exact_mod_cast h
    have hr1 : (0 : ℚ) < (Fintype.card A : ℚ) - 1 := by linarith
    have ht : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
    field_simp [hr.ne', hr1.ne', ht.ne']

private theorem sum_bool_rat (f : Bool → ℚ) : (∑ b, f b) = f false + f true := by
  have hh : (Finset.univ : Finset Bool) = {false,true} := by
    ext b; cases b <;> simp
  rw [hh, Finset.sum_insert (by simp), Finset.sum_singleton]

theorem total_marginal_sum (h : 2 ≤ Fintype.card A) (ref : Seed A R)
    (row : W → Row) (col : W → OrdinaryColumn Pair Col) (c : Word A R × Word A R) :
    (∑ e : Wire Pair W, meanCell (law A R Pair Row Col) (fullCell row col) e c) =
      (Fintype.card (Wire Pair W) : ℚ) / denom A R := by
  simp_rw [full_marginal (ref.2 (0,0)) row col]
  rw [← Finset.sum_mul, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have L (p : Pin Pair) :
      (∑ k : Bool, chosenMean row col (.inl (p,k)) (c.1.1,c.2.1)) =
        2 / (Fintype.card A : ℚ)^2 := by
    rw [sum_bool_rat, chosenMean_pin h, chosenMean_mate h]
    simpa only [uniform, qSize, joint_pin_edge h, joint_clone_edge h] using
      combined_cell_load h c.1.1 c.2.1
  simp_rw [L, chosenMean_regular h ref.1]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    uniform, denom]
  have hr : (0 : ℚ) < Fintype.card A := by exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ 1) h)
  have ht : (0 : ℚ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  field_simp [hr.ne', ht.ne']

section Certificate

variable [AddCommGroup A]

omit [Fintype A] [Fintype R] [Nonempty R] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] in
theorem fullCell_depends (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (e : Wire Pair W) (z z' : State A R Pair Row Col)
    (h : ∀ b ∈ blockSupport row col e, z b = z' b) :
    fullCell row col e z = fullCell row col e z' := by
  have hz := (cell_depends_on_support row col (fun b => toDraw (z b).1) (fun b => toDraw (z' b).1)
    e (fun b hb => congrArg (fun t : Seed A R => toDraw t.1) (h b hb)))
  have hx : chosenCell row col (fun b => (z b).1) e = chosenCell row col (fun b => (z' b).1) e := by
    rw [chosenCell_eq_cell, chosenCell_eq_cell]
    exact hz
  have ht := tailPorts_support row col e
  have hy : tailCell row col (fun b => (z b).2) e = tailCell row col (fun b => (z' b).2) e := by
    unfold tailCell
    generalize hv : tailPorts row col e = v at ht ⊢
    rcases v with ⟨a,b⟩
    dsimp only at ht ⊢
    rw [h _ ht.1, h _ ht.2]
  unfold fullCell
  rw [hx, hy]

omit [Fintype A] [Fintype R] [Nonempty R] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] in
theorem full_indicator_depends (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (e : Wire Pair W) (c : Word A R × Word A R) :
    depends (fun b => b ∈ blockSupport row col e) (fun z => indicator (fullCell row col e z) c) := by
  intro z z' hz
  exact congrArg (fun x => indicator x c) (fullCell_depends row col e z z' hz)

omit [Nonempty R] [Fintype W] in
/-- The full ordered-cell evaluation still reads at most four original
blocks for a pair of wires, even though each block now has complete words. -/
theorem full_conditional_pair (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (w : Block Pair Row Col → Seed A R → ℚ) (h : ∀ b, ∑ z, w b z = 1)
    (ref : State A R Pair Row Col) (e f : Wire Pair W) (c : Word A R × Word A R) :
    let s := blockSupport row col e ∪ blockSupport row col f
    let g := fun z => indicator (fullCell row col e z) c * indicator (fullCell row col f z) c
    s.card ≤ 4 ∧ average w g =
      average (fun b : {b // b ∈ s} => w b) (fun t => g (fill (fun b => b ∈ s) ref t)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · convert pair_support_at_most_four row col e f using 1
    congr 1
    exact Finset.ext fun b => by simp only [Finset.mem_union]
  have hlocal : depends (fun b => b ∈ blockSupport row col e ∪ blockSupport row col f)
      (fun z => indicator (fullCell row col e z) c * indicator (fullCell row col f z) c) := by
    intro z z' hz
    exact congrArg₂ (· * ·)
      (full_indicator_depends row col e c z z' (fun b hb => hz b (Finset.mem_union_left _ hb)))
      (full_indicator_depends row col f c z z' (fun b hb => hz b (Finset.mem_union_right _ hb)))
  convert expectation_only_support w h _ ref _ hlocal using 1
  congr 1
  exact Subsingleton.elim _ _

theorem full_expected_bound (h : 2 ≤ Fintype.card A)
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_cap : ∀ r, (Finset.univ.filter fun w : W => row w = r).card ≤ 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3)
    (reference : State A R Pair Row Col) (s : Finset (Wire Pair W)) :
    average weight (varianceScore s (law A R Pair Row Col) (fullCell row col)) ≤
      16 * (Fintype.card (Wire Pair W) : ℚ) := by
  have hn : ∀ i : Block Pair Row Col, ∑ z : Seed A R, weight i z = 1 := weight_normalized h
  have hp : ∀ i : Block Pair Row Col, ∀ z : Seed A R, 0 ≤ weight i z := weight_nonneg h
  have hbase := expected_score_le_dependent (s := s) (weight := law A R Pair Row Col)
    (label := fullCell row col) (dependentOn row col)
    (productWeight_nonneg weight hp) (productWeight_normalized weight hn)
  have hind : ∀ e ∈ s, ∀ f ∈ s, f ∉ dependentOn row col e → ∀ c,
      expect (law A R Pair Row Col)
        (fun z => indicator (fullCell row col e z) c * indicator (fullCell row col f z) c) =
        meanCell (law A R Pair Row Col) (fullCell row col) e c *
          meanCell (law A R Pair Row Col) (fullCell row col) f c := by
    intro e _ f _ hd c
    have hdis : ∀ b, b ∈ blockSupport row col e → b ∈ blockSupport row col f → False :=
      fun b he hf => hd ((mem_dependentOn row col e f).2 ⟨b,he,hf⟩)
    simpa only [average, meanCell] using
      expectation_disjoint_supports weight hn _ _ hdis reference _ _
        (full_indicator_depends row col e c) (full_indicator_depends row col f c)
  have hfull : (∑ e : Wire Pair W, ((dependentOn row col e).card : ℚ)) ≤
      16 * (Fintype.card (Wire Pair W) : ℚ) := by
    have hnat : (∑ e : Wire Pair W, (dependentOn row col e).card) ≤ 16 * Fintype.card (Wire Pair W) := by
      exact ordered_dependent_pairs_le16 row col row_cap clone_cap col_cap
    exact_mod_cast hnat
  exact (hbase hind).trans <|
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun _ _ _ => Nat.cast_nonneg _)).trans hfull

omit [Nonempty R] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] [AddCommGroup A] in
theorem legal_pinOff (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : State A R Pair Row Col) (hz : ∀ b, 0 < weight b (z b))
    (p : Pin Pair) :
    (fullCell row col (pinEmbed Pair W p) z).1.1 ≠
      (fullCell row col (pinEmbed Pair W p) z).2.1 := by
  rcases p with ⟨p,s⟩
  simp only [pinEmbed, Function.Embedding.coeFn_mk, fullCell, chosenCell, Bool.false_eq_true, if_false]
  intro he
  have hpos := hz (.inl p)
  by_cases hs : s = 0
  · have hh : pairLaw (z (.inl p)).1.1 (z (.inl p)).1.2.1 = 0 := by
      simp only [gadget, hs, if_true] at he
      simp [pairLaw, rowKernel, he]
    simp [weight, chosenWeight, hh] at hpos
  · have hh : pairLaw (z (.inl p)).1.1 (z (.inl p)).1.2.2 = 0 := by
      simp only [gadget, hs, if_false] at he
      simp [pairLaw, rowKernel, he]
    simp [weight, chosenWeight, hh] at hpos

/-- Actual full words satisfy simultaneously the finite total-load and
pin-load variance budgets, with the exact unconditioned means written out.
All the distinguished pin cells are guaranteed off-diagonal. -/
theorem full_supported_selection (h : 2 ≤ Fintype.card A)
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_cap : ∀ r, (Finset.univ.filter fun w : W => row w = r).card ≤ 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3)
    (reference : State A R Pair Row Col) (ref : Seed A R) :
    ∃ z : State A R Pair Row Col,
      (∀ b, 0 < weight b (z b)) ∧
      (∀ p : Pin Pair, (fullCell row col (pinEmbed Pair W p) z).1.1 ≠
        (fullCell row col (pinEmbed Pair W p) z).2.1) ∧
      varianceScore Finset.univ (law A R Pair Row Col) (fullCell row col) z +
        varianceScore (pinWires Pair W) (law A R Pair Row Col) (fullCell row col) z ≤
          32 * (Fintype.card (Wire Pair W) : ℚ) ∧
      ∀ c : Word A R × Word A R,
        ((∑ e : Wire Pair W, indicator (fullCell row col e z) c) -
          (Fintype.card (Wire Pair W) : ℚ) / denom A R)^2 ≤
          32 * (Fintype.card (Wire Pair W) : ℚ) ∧
        ((∑ e ∈ pinWires Pair W, indicator (fullCell row col e z) c) -
          (if c.1.1 = c.2.1 then 0 else ((Fintype.card A : ℚ) / (Fintype.card A - 1)) *
            ((Fintype.card (Pin Pair) : ℚ) / denom A R)))^2 ≤
          32 * (Fintype.card (Wire Pair W) : ℚ) := by
  let F := varianceScore Finset.univ (law A R Pair Row Col) (fullCell row col)
  let G := varianceScore (pinWires Pair W) (law A R Pair Row Col) (fullCell row col)
  have hnorm : ∀ i : Block Pair Row Col, ∑ z : Seed A R, weight i z = 1 := weight_normalized h
  obtain ⟨z,hz,hscore⟩ := J7SourceAssembly.exists_legal_labeling_by_conditioning
    reference weight (weight_nonneg h) hnorm (fun z => F z + G z)
  rw [GuardExpectation.average_add] at hscore
  have hf := full_expected_bound h row col row_cap clone_cap col_cap reference Finset.univ
  have hg := full_expected_bound h row col row_cap clone_cap col_cap reference (pinWires Pair W)
  have hFG : F z + G z ≤ 32 * (Fintype.card (Wire Pair W) : ℚ) := by
    change F z + G z ≤ average weight F + average weight G at hscore
    change average weight F ≤ _ at hf
    change average weight G ≤ _ at hg
    linarith
  refine ⟨z,hz,legal_pinOff row col z hz,hFG,?_⟩
  intro c
  have hF0 : 0 ≤ F z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG0 : 0 ≤ G z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hFc : (∑ e : Wire Pair W, centered (law A R Pair Row Col) (fullCell row col) e c z)^2 ≤ F z :=
    Finset.single_le_sum (f := fun c =>
      (∑ e : Wire Pair W, centered (law A R Pair Row Col) (fullCell row col) e c z)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  have hGc : (∑ e ∈ pinWires Pair W, centered (law A R Pair Row Col) (fullCell row col) e c z)^2 ≤ G z :=
    Finset.single_le_sum (f := fun c =>
      (∑ e ∈ pinWires Pair W, centered (law A R Pair Row Col) (fullCell row col) e c z)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  simp only [centered, Finset.sum_sub_distrib, total_marginal_sum h ref row col] at hFc
  simp only [centered, Finset.sum_sub_distrib, pin_marginal_sum h (ref.2 (0,0)) row col] at hGc
  exact ⟨hFc.trans (by linarith),hGc.trans (by linarith)⟩

end Certificate

#print axioms denom_coordinates
#print axioms pin_marginal_sum
#print axioms total_marginal_sum
#print axioms fullCell_depends
#print axioms full_conditional_pair
#print axioms full_expected_bound
#print axioms legal_pinOff
#print axioms full_supported_selection

end
end J7FullWordAssembly
