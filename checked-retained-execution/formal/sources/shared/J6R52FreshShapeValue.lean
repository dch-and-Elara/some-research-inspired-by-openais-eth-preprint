import J6R52FreshShapeCore
import J7R10Plant

/-! Source semantics required by the old root terminal: the new
actual chart still has the legal all-zero opening, and its literal
layer polynomial at one is the guarded CNF count. No equality of two
independently numbered layer-polynomial coefficient arrays is used. -/
namespace J6R52FreshShape
open scoped Classical Polynomial BigOperators
open Std.Sat J7R9Compiler J7R9Subdivision J7R10Plant J6OrientedHostEval
open J6R51Ingress
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 11600000

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V]
variable (F : CNF V) (order : DeclaredOrder V)
local notation "H" => (guardedInOrder F order.roster)
local notation "S" => (guardRoster order)
local notation "T" => (freshPlant H S)
local notation "m" => (nWires H)

theorem submitted_guard_all_zero :
    CNF.Sat (fun _ : Option V=>false) H := by
  have e := ordered_guard_perm F order.roster order.distinct order.complete
  have h := J6Guard.all_zero_model (J7R9Clause.clean F)
  unfold CNF.Sat CNF.eval at h ⊢
  simp only [List.all_eq_true,e.mem_iff]
  exact List.all_eq_true.mp h

theorem submitted_bipolar_zero :
    bipolarOK H (fun _ : Half H=>false) := by
  change bipolarOK H (lift H (encode H (fun _ : Option V=>false)))
  rw [network_under_lift,encode_ok]
  exact submitted_guard_all_zero F order

theorem actual_fresh_zero_opening :
    coreA T (fun _=>false)=true ∧ coreB T (fun _=>false)=true := by
  apply (fresh_plant_exact H S (fun _=>false)).mpr
  change bipolarOK H (fun _ : Half H=>false)
  exact submitted_bipolar_zero F order

theorem actual_fresh_layer_origin [Nonempty V] :
    (LayerRecovery.layerPolynomial (J6OrientedPlantValue.wt (coreA T))
      (J6OrientedPlantValue.wt (coreB T))).eval 1 =
        (1+PinnedCNF.modelCount F:ℕ) := by
  have cnt := fresh_submitted_CNF_count F order S
  dsimp only at cnt
  rw [LayerRecovery.layerPolynomial_eval_one,←cnt,←Fintype.card_eq_nat_card]
  rw [Fintype.card_subtype,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  unfold J6OrientedPlantValue.wt
  cases coreA T x <;> cases coreB T x <;> simp

#print axioms submitted_guard_all_zero
#print axioms submitted_bipolar_zero
#print axioms actual_fresh_zero_opening
#print axioms actual_fresh_layer_origin
end
end J6R52FreshShape
