import J6R112GuardedInputBindingBase
import J6R112ExecutedSelectedStartupRun

/-! Discharge precisely the two guarded-count premises on the same
actual startup image. No second word-producing program is invoked. -/
namespace J6R112GuardedInputBinding
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime J6Mesh
open J7R10Plant J6OrientedHostEval J6R51Ingress J6R52FreshShape
open J6R111FreshStartupBinding J6R112ExecutedSelectedStartup

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 4200
set_option maxHeartbeats 11000000
set_option maxSynthPendingDepth 8

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {order : DeclaredOrder V}
local notation "Graph" => (guardedInOrder F order.roster)
local notation "m" => (nWires Graph)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)
local notation "s" => (physicalSize m n)
variable {h d j r c e base ell kp : ℕ}

theorem actual_fresh_startup_count_is_the_submitted_CNF
    (A : RawStartup F order h d j r c e base ell kp)
    (fit : base≤s^2) (plan : StartupSelection A fit) (basePositive : 0<base) :
    bitsValue (runWithActualFreshStartup A fit plan).result.val=PinnedCNF.modelCount F := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot := selectedStartup A fit
  obtain ⟨zero,count⟩ := ordered_original_input_supplies_its_own_count_and_opening F order
  change bitsValue (countOnThatImage boot.result plan).result.val=PinnedCNF.modelCount F
  exact the_selected_image_count_is_the_guarded_count boot.result plan basePositive zero
    (PinnedCNF.modelCount F) count

#print axioms actual_fresh_startup_count_is_the_submitted_CNF
end
end J6R112GuardedInputBinding
