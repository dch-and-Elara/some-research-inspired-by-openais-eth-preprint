import J7R10Counts
import J7R9SourceInput
import J6OrientedHostCounts
import J6OrientedPlantValue

/-!
# Concrete J6 Plant from the literal half-wire chart

The actual source old and new tables are installed in the already
verified J6 Plant interface. Numbering is a separate finite
reindexing; it does not assume equal contractions, full degree,
or a precomputed assignment count.
-/

open Std.Sat
open scoped BigOperators Polynomial

namespace J7R10Plant
open J7R9Compiler J7R9Subdivision J7R10Ports J7R10Counts
open J6OrientedHost J6OrientedHostEval J6RecursivePortCube
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def nWires (F : CNF V) : ℕ := Fintype.card (Half F)
noncomputable def nSubdiv (F : CNF V) : ℕ := Fintype.card (J7R9Compiler.Wire F)

theorem twice_subdiv (F : CNF V) :
    nWires F = 2*nSubdiv F := by
  unfold nWires nSubdiv
  rw [Fintype.card_prod,Fintype.card_bool,mul_comm]

noncomputable def wireNumber (F : CNF V) :
    Half F ≃ Fin (nWires F) := Fintype.equivFin _

noncomputable def subdivNumber (F : CNF V) :
    J7R9Compiler.Wire F ≃ Fin (nSubdiv F) := Fintype.equivFin _

noncomputable def physicalPlant (F : CNF V) :
    Plant (Old F) (nWires F) (nSubdiv F) where
  degree := degree F
  old := gate F
  rowPort := (rowChart F).trans (wireNumber F)
  colPort := (Equiv.prodCongr (subdivNumber F).symm (Equiv.refl Bool)).trans (wireNumber F)

theorem plant_row (F : CNF V) (p : OldPort F) :
    (physicalPlant F).rowPort p = wireNumber F (read F p) := rfl

theorem plant_column (F : CNF V) (w : J7R9Compiler.Wire F) (b : Bool) :
    (physicalPlant F).colPort (subdivNumber F w,b) = wireNumber F (w,b) := by
  simp [physicalPlant]

/-- The exact assignment equivalence induced by physical numbering,
not by matching convenient labels of the raw graph. -/
noncomputable def assignmentChart (F : CNF V) :
    (Fin (nWires F) → Bool) ≃ (Half F → Bool) where
  toFun x := fun w => x (wireNumber F w)
  invFun x := fun n => x ((wireNumber F).symm n)
  left_inv x := funext fun w => by simp
  right_inv x := funext fun w => by simp

theorem coreA_physical (F : CNF V) (x : Fin (nWires F) → Bool) :
    coreA (physicalPlant F) x=true ↔ physicalOldOK F (assignmentChart F x) := by
  unfold coreA good
  rw [decide_eq_true_eq, ← old_gate_evaluation]
  rfl

theorem coreB_physical (F : CNF V) (x : Fin (nWires F) → Bool) :
    coreB (physicalPlant F) x=true ↔ newOK F (assignmentChart F x) := by
  unfold coreB good
  simp only [decide_eq_true_eq, newOK]
  constructor
  · intro h w
    have hw := h (subdivNumber F w)
    rw [plant_column,plant_column] at hw
    exact hw
  · intro h i
    obtain ⟨w,rfl⟩ := (subdivNumber F).surjective i
    rw [plant_column,plant_column]
    exact h w

theorem plant_iff (F : CNF V) (x : Fin (nWires F) → Bool) :
    (coreA (physicalPlant F) x=true ∧ coreB (physicalPlant F) x=true) ↔
      bipolarOK F (assignmentChart F x) :=
  Iff.and (coreA_physical F x) (coreB_physical F x)

noncomputable def acceptingChart (F : CNF V) :
    {x : Fin (nWires F) → Bool //
      coreA (physicalPlant F) x=true ∧ coreB (physicalPlant F) x=true}
    ≃ {x : Half F → Bool // bipolarOK F x} where
  toFun x := ⟨assignmentChart F x.val,(plant_iff F x.val).mp x.property⟩
  invFun x := ⟨(assignmentChart F).symm x.val,(plant_iff F _).mpr (by
    rw [Equiv.apply_symm_apply]
    exact x.property)⟩
  left_inv x := Subtype.ext ((assignmentChart F).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((assignmentChart F).apply_symm_apply x.val)

theorem plant_count (F : CNF V) (h : AllOccur F) :
    Nat.card {x : Fin (nWires F) → Bool //
      coreA (physicalPlant F) x=true ∧ coreB (physicalPlant F) x=true} =
      PinnedCNF.modelCount F := by
  rw [Nat.card_congr (acceptingChart F),subdivision_count F h]

theorem planted_guard_zero [Nonempty V] (F : CNF V) :
    coreA (physicalPlant (J7R9SourceInput.H F)) (fun _ => false)=true := by
  let H := J7R9SourceInput.H F
  apply (coreA_physical H (fun _ => false)).mpr
  have hg : CNF.Sat (fun _ => false) H := J6Guard.all_zero_model (J7R9Clause.clean F)
  have ho := (encode_ok H (fun _ => false)).mpr hg
  exact ((old_under_lift H (encode H (fun _ => false))).mpr ho)

theorem planted_guard_degree (F : CNF V) (h : ∀ c ∈ F, c.length≤3)
    (v : Old (J7R9SourceInput.H F)) :
    (physicalPlant (J7R9SourceInput.H F)).degree v ≤ 4 := by
  exact degree_bound _ 4 (J7R9SourceInput.width_four F h) v

/-- This is the old layer polynomial consumed by the R8 receiver,
with no remaining external count-preservation assertion. -/
theorem origin_exact (F : CNF V) (h : AllOccur F) :
    (LayerRecovery.layerPolynomial (J6OrientedPlantValue.wt (coreA (physicalPlant F)))
      (J6OrientedPlantValue.wt (coreB (physicalPlant F)))).eval 1 =
      (PinnedCNF.modelCount F:ℚ) := by
  classical
  rw [LayerRecovery.layerPolynomial_eval_one, ← plant_count F h,←Fintype.card_eq_nat_card]
  rw [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  unfold J6OrientedPlantValue.wt
  cases coreA (physicalPlant F) x <;> cases coreB (physicalPlant F) x <;> simp

theorem guarded_origin_exact [Nonempty V] (F : CNF V) :
    let H := J7R9SourceInput.H F
    (LayerRecovery.layerPolynomial (J6OrientedPlantValue.wt (coreA (physicalPlant H)))
      (J6OrientedPlantValue.wt (coreB (physicalPlant H)))).eval 1 =
      (1+PinnedCNF.modelCount F:ℕ) := by
  dsimp only
  rw [origin_exact (J7R9SourceInput.H F) (guard_allOccur (J7R9Clause.clean F))]
  exact congrArg (fun n : ℕ => (n:ℚ)) (J7R9Clause.guarded_clean_count F)

#print axioms plant_row
#print axioms plant_column
#print axioms plant_iff
#print axioms plant_count
#print axioms planted_guard_zero
#print axioms planted_guard_degree
#print axioms origin_exact
#print axioms guarded_origin_exact

end J7R10Plant

