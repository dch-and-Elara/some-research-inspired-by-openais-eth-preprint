import J7R13Score
import J7ToJ8Layout
import J6R10RepackRounded

/-! Whole-word incidence and the source's collision objective, on the same wires as J8. -/
open scoped Classical BigOperators
namespace J7R13
open J7SourceLabels J7FullWordCells J7FullWordLaw J7FullWordAssembly J7FullWordPrinted
open J7SourceConditioning J7SeatSource J7ToJ8Incidence J7ToJ8Layout P11FullPacking
noncomputable section

local instance (priority := 100000) : DecidableEq Slot :=
  fun _ _ => Classical.propDecidable _

local instance (priority := 100000) {P R C : Type*} : DecidableEq (Block P R C) :=
  fun _ _ => Classical.propDecidable _

variable {A Pair Row Col W : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t : ℕ}

def network (row : W → Row) (col : W → OrdinaryColumn Pair Col) :
    J6R10Repack.Network (Wire Pair W) (Subdivision Pair Row) (Pin Pair ⊕ OrdinaryColumn Pair Col) :=
  ⟨rowNode row,colNode col⟩

def rowFull (z : DState A Pair Row Col t) : Subdivision Pair Row → Fin (t+1) → A
  | .inl (p,s) => wordEquiv A t ((gadget (z (.inl p)).1 s).1,(z (.inl p)).2 (s,1))
  | .inr r => wordEquiv A t ((z (.inr (.inl r))).1.1,(z (.inr (.inl r))).2 (0,0))

def colFull (z : DState A Pair Row Col t) : Pin Pair ⊕ OrdinaryColumn Pair Col → Fin (t+1) → A
  | .inl (p,s) => wordEquiv A t ((z (.inl p)).1.1,(z (.inl p)).2 (s,0))
  | .inr (.inl (p,s)) => wordEquiv A t ((gadget (z (.inl p)).1 s).2,(z (.inl p)).2 (s,2))
  | .inr (.inr c) => wordEquiv A t ((z (.inr (.inr c))).1.1,(z (.inr (.inr c))).2 (0,0))

omit [LinearOrder A] [AddCommGroup A] [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] in
theorem rowFull_head (z : DState A Pair Row Col t) (v : Subdivision Pair Row) :
    rowFull z v 0 = subdivisionHead z v := by
  rcases v with ⟨p,s⟩|r <;> simp [rowFull,subdivisionHead,wordEquiv_retained]

omit [LinearOrder A] [AddCommGroup A] [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] in
theorem colFull_head (z : DState A Pair Row Col t) (v : Pin Pair ⊕ OrdinaryColumn Pair Col) :
    colFull z v 0 = Sum.elim (pinHead z) (columnHead z) v := by
  rcases v with ⟨p,s⟩|(⟨p,s⟩|c) <;> simp [colFull,pinHead,columnHead,wordEquiv_retained]

omit [LinearOrder A] [AddCommGroup A] [Fintype A] in
private theorem chart_at (w : Word A (Fin t → A) × Word A (Fin t → A)) (i : Fin (t+1)) :
    cellChartEq A t w i = (wordEquiv A t w.1 i,wordEquiv A t w.2 i) := rfl

omit [LinearOrder A] [AddCommGroup A] [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] in
theorem actual_cell (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : DState A Pair Row Col t) (w : Wire Pair W) :
    wordLabel row col z w = J6R10Repack.declaredCell (network row col) (rowFull z) (colFull z) w := by
  funext i
  rcases w with ⟨⟨p,s⟩,b⟩|w
  · cases b <;> simp [wordLabel, chart_at, J6R10Repack.declaredCell, network, rowNode, colNode,
      rowFull, colFull, fullCell, chosenCell, tailCell, tailPorts]
  · cases h : col w with
    | inl p =>
      obtain ⟨p,s⟩ := p
      simp [wordLabel, chart_at, J6R10Repack.declaredCell, network, rowNode, colNode, h,
        rowFull, colFull, fullCell, chosenCell, tailCell, tailPorts]
    | inr c =>
      simp [wordLabel, chart_at, J6R10Repack.declaredCell, network, rowNode, colNode, h,
        rowFull, colFull, fullCell, chosenCell, tailCell, tailPorts]

omit [LinearOrder A] [AddCommGroup A] [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] in
/-- Both physical legs of a given binary old column carry its identical
full column word. This remains valid on larger fibres, without treating
the actual ternary equality columns as binary. -/
theorem same_column_words (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : DState A Pair Row Col t) {x y : Wire Pair W}
    (h : colNode col x = colNode col y) (i : Fin (t+1)) :
    (wordLabel row col z x i).2 = (wordLabel row col z y i).2 := by
  rw [actual_cell row col z x,actual_cell row col z y]
  change colFull z (colNode col x) i = colFull z (colNode col y) i
  rw [h]

omit [LinearOrder A] [AddCommGroup A] in
theorem word_cell_denominator :
    ((Nat.card (Cell (Fin (t+1)) A) : ℕ) : ℚ) = denom A (Fin t → A) := by
  rw [total_cells,denom_coordinates,Nat.cast_pow]

omit [AddCommGroup A] [Fintype A] [Fintype Row] [Fintype Col] in
theorem load_chart (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : DState A Pair Row Col t) (c : Word A (Fin t → A) × Word A (Fin t → A)) :
    (Nat.card (J6R10Repack.Fiber (wordLabel row col z) (cellChartEq A t c)) : ℚ) =
      ∑ e : Wire Pair W, indicator (fullCell row col e z) c := by
  rw [cast_card_eq_indicator]
  exact Finset.sum_congr rfl fun e _ => by simp [wordLabel,indicator]

set_option maxHeartbeats 1600000 in
theorem collision_exact (h : 2 ≤ Fintype.card A) (row : W → Row)
    (col : W → OrdinaryColumn Pair Col)
    (z : DState A Pair Row Col t) (ref : Seed A (Fin t → A)) :
    J6R10Repack.varianceScore (wordLabel row col z) =
      J7SourceConditioning.varianceScore Finset.univ (law A (Fin t → A) Pair Row Col)
        (fullCell row col) z := by
  symm
  unfold J6R10Repack.varianceScore J7SourceConditioning.varianceScore
  refine Fintype.sum_equiv (cellChartEq A t) _ _ (fun c => ?_)
  simp only [centered, Finset.sum_sub_distrib, total_marginal_sum h ref row col]
  rw [load_chart row col z c, word_cell_denominator, Nat.card_eq_fintype_card (α:=Wire Pair W)]

/-- The ordinary full-word objective is below the original two-objective
score, because the pin-only variance is a sum of squares. -/
theorem collision_of_joint (h : 2 ≤ Fintype.card A) (row : W → Row)
    (col : W → OrdinaryColumn Pair Col) (z : DState A Pair Row Col t)
    (ref : Seed A (Fin t → A)) (Δ : ℕ) (hΔ : 16 ≤ Δ)
    (hscore : JointScore row col z ≤ 32 * (Fintype.card (Wire Pair W) : ℚ)) :
    J6R10Repack.varianceScore (J6R10Repack.declaredCell (network row col) (rowFull z) (colFull z)) ≤
      2*(Nat.card (Wire Pair W):ℚ)*Δ := by
  rw [← funext (actual_cell row col z),collision_exact h row col z ref]
  have hp : 0 ≤ J7SourceConditioning.varianceScore (pinWires Pair W)
      (law A (Fin t → A) Pair Row Col) (fullCell row col) z := by
    unfold J7SourceConditioning.varianceScore
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hq : (16:ℚ) ≤ Δ := by exact_mod_cast hΔ
  rw [Nat.card_eq_fintype_card]
  exact ((le_add_of_nonneg_right hp).trans hscore).trans (by
    calc
      _ = 2*(Fintype.card (Wire Pair W):ℚ)*16 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity))

#print axioms rowFull_head
#print axioms colFull_head
#print axioms actual_cell
#print axioms same_column_words
#print axioms word_cell_denominator
#print axioms load_chart
#print axioms collision_exact
#print axioms collision_of_joint

end
end J7R13
