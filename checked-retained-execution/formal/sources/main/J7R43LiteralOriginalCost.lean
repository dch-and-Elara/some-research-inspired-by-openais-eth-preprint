import J7R43LiteralCost
import J9R20SameFileLiteralTables

/-! The exact J7 marginal-visit trace specializes to the actual printed
four-clone old gates. Their port counts are 2 or 3, not an independent
runtime promise or a bound inferred from a number of matrices. -/
namespace J7R43Literal
open scoped Classical
open J7SourceLabels J7PrintedParamsGraph J7ToJ8Incidence J8Physical J9R20SameFile
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14000000
set_option quotPrecheck false
set_option maxRecDepth 5000
local instance (priority := 16000) j7CostGroupEq : DecidableEq (Fin 64) :=
  fun x y => Classical.propDecidable (x=y)

variable {Pair H Packet R : Type} [Fintype Pair] [Fintype H] [Fintype Packet] [Fintype R]
variable {L : ℕ}
variable (ends : H×Bool≃Pin Pair×Fin 3)
variable (d : Layout Packet R (Pin Pair) (PrintedOld Pair H) (Fin 64) (Ports (column ends cycle)) L)
local notation "D" => PrintedOld Pair H
local notation "M" => Fintype.card (J8Physical.Wire R)

private theorem original_degree_range (v : D) :
    0 < Nat.card (Ports (column ends cycle) v) ∧ Nat.card (Ports (column ends cycle) v) ≤ 3 := by
  rw [printed_old_arity ends]
  rcases v with _|(_|_) <;> first
    | exact (by decide : 0<(3:ℕ) ∧ 3≤3)
    | exact (by decide : 0<(2:ℕ) ∧ 2≤3)

include d in
theorem original_old_columns_le_real_wires : Fintype.card D ≤ M := by
  let em (v : D) := ordinaryWire d ⟨v,Classical.choice (Nat.card_pos_iff.mp (original_degree_range ends v).1).1⟩
  refine Fintype.card_le_of_injective em ?_
  intro x y h
  have hu := d.column.symm.injective h
  exact congrArg Sigma.fst (Sum.inr.inj hu)

theorem original_old_tile_le_real_wires (s : Pin Pair) :
    Fintype.card (OldTile d s) ≤ M := by
  let em (x : OldTile d s) := ordinaryWire d x.val
  refine Fintype.card_le_of_injective em ?_
  intro x y h
  exact Subtype.ext (Sum.inr.inj (d.column.symm.injective h))

theorem original_baseline_old_visit_bound (g : Fin 64) :
    (actualBaselineVisits d g).length ≤ 8*M := by
  have hdeg (v : D) : Fintype.card (Ports (column ends cycle) v) ≤ 3 :=
    (@Nat.card_eq_fintype_card (Ports (column ends cycle) v) _).symm.trans_le (original_degree_range ends v).2
  have hcols : Fintype.card (LocalColumn d g) ≤ M :=
    (Fintype.card_le_of_injective (fun v : LocalColumn d g => v.val) Subtype.val_injective).trans (original_old_columns_le_real_wires ends d)
  calc
    _ ≤ Fintype.card (LocalColumn d g)*2^3 := baselineVisits_bounded_degree d g 3 hdeg
    _ ≤ M*2^3 := Nat.mul_le_mul_right _ hcols
    _ = 8*M := Nat.mul_comm M 8

theorem original_source_old_visit_bound (s : Pin Pair) :
    (actualSourceVisits d s).length ≤ (M+1)*(8*M) := by
  rw [sourceVisits_length]
  exact Nat.mul_le_mul (Nat.add_le_add_right (original_old_tile_le_real_wires ends d s) 1)
    (original_baseline_old_visit_bound ends d (d.pinLabel s))

#print axioms original_old_columns_le_real_wires
#print axioms original_old_tile_le_real_wires
#print axioms original_baseline_old_visit_bound
#print axioms original_source_old_visit_bound
end
end J7R43Literal
