import J6R55PublicDemand

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8500000
set_option Elab.async false
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false

/-! Analytic tariff at the seam between the genuine mounted recipe
and the raw callback. No recipe is re-evaluated by this comparison, and
the lookup and reply operation in the actual provider remain the same. -/
namespace J6R55Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R25PreparedSupply J6R34ChildPath J6R49DFS
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS J6R51Online
open J6R50SourceProducer J6R52Dispatch J6R53Dispatch J6R54Dispatch J6R55Public
noncomputable section

private theorem meter_eq_fields {A : Type*} {a b : Meter A}
    (result : a.result=b.result) (steps : a.steps=b.steps) : a=b := by
  cases a with
  | mk a₀ af =>
    cases b with
    | mk b₀ bf =>
      cases result
      cases steps
      rfl

variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child}
variable (input : Meter (FixedRequest X w))

def billedRecipePicker : FixedPicker input.result.replay :=
  fun raw g =>
    let request := input.result.find raw g
    ⟨request.result,input.steps+request.steps+3⟩

def recipeHit : FixedCarrier input.result.replay input.result.raw input.result.group :=
  (input.result.find input.result.raw input.result.group).result.get input.result.hit

theorem recipe_picker_exact_option :
    (billedRecipePicker input input.result.raw input.result.group).result=some (recipeHit input) :=
  (Option.some_get input.result.hit).symm

theorem actual_selected_recipe_is_whole_raw_demand :
    meteredSelectedDemand input=
      mountedDemand input.result.replay (billedRecipePicker input) (recipeHit input)
        (usingParentIssuer input.result.replay input.result.shell)
        (usingParentIssuerDirectory input.result.replay input.result.shell input.result.directory) := by
  apply meter_eq_fields
  · rfl
  · let A := input.result
    let K := (recipeHit input).val.load (usingParentIssuer A.replay A.shell)
      (usingParentIssuerDirectory A.replay A.shell A.directory)
    change input.steps+((A.find A.raw A.group).steps+K.steps+4)+3=
      (input.steps+(A.find A.raw A.group).steps+3)+K.steps+4
    omega

variable (M : OnlineMachine T key prec tw bw page rate)
variable (req : ∀ {v : Ticket sel root} (X : StoredSite T v key prec tw bw page)
  (u : (Plan sel).Slot v.child),Meter (FixedRequest X u))

theorem mounted_machine_executes_its_billed_recipe :
    let A := req X w
    (withSelectedDemands M req).demand X w=
      mountedDemand A.result.replay (billedRecipePicker A) (recipeHit A)
        (usingParentIssuer A.result.replay A.result.shell)
        (usingParentIssuerDirectory A.result.replay A.result.shell A.result.directory) :=
  actual_selected_recipe_is_whole_raw_demand (req X w)

#print axioms recipe_picker_exact_option
#print axioms actual_selected_recipe_is_whole_raw_demand
#print axioms mounted_machine_executes_its_billed_recipe
end
end J6R55Dispatch
