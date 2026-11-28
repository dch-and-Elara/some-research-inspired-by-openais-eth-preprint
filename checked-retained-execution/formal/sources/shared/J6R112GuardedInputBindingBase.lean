import J6R52FreshShapeValue

/-! The exact guarded input of the fresh R54/R111 startup, not an
unordered substitute. Both acceptance facts are inherited from the
already verified source circuit and the declared ordering. -/
namespace J6R112GuardedInputBinding
open scoped Classical
open Std.Sat J7R10Plant J6OrientedHostEval J6R51Ingress J6R52FreshShape

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 4800000

noncomputable section
theorem ordered_original_input_supplies_its_own_count_and_opening
    {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (F : CNF V) (order : DeclaredOrder V) :
    let H := guardedInOrder F order.roster
    let P := freshPlant H (guardRoster order)
    coreA P (fun _=>false)=true ∧
      Nat.card {x : Fin (nWires H)→Bool // coreA P x=true ∧ coreB P x=true}=
        1+PinnedCNF.modelCount F :=
  ⟨(actual_fresh_zero_opening F order).1,fresh_submitted_CNF_count F order (guardRoster order)⟩

#print axioms ordered_original_input_supplies_its_own_count_and_opening
end
end J6R112GuardedInputBinding
