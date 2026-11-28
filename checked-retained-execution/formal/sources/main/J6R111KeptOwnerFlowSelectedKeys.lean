import J6R111KeptOwnerFlowSelected
import J6R55PublicDemand
import J6R102NativeCodeMeterDemand

/-! The precise extra compatibility premise on the chosen fixed
request. Width and names must belong to its same raw directory. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R24MeteredRecursion
open J6R26DescriptorTree J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R50SourceProducer J6R51Online J6R55Public J6R102NativeCodeMeter
open J6R94HeldOwnerProvider J6R58RequestSource
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18500000
set_option maxRecDepth 4750
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {Y : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child}
variable (request : Meter (FixedRequest Y u))

/-- Changing the issuing key and choosing the paid ordinal width in the
R55→R102 path keep the exact old-key context written in that request's
directory. No true gate tape is reconstructed from it. -/
theorem fixed_request_key_context_is_the_actual_charged_successor_context :
    let loaded := (meteredSelectedDemand request).bind measureLocalLoad
    namesAsRawContext loaded.result.advance.next.site.oldKey=
      namesAsRawContext request.result.directory.oldKey := rfl

theorem a_fixed_request_with_literal_owner_keys_fills_the_selected_guard
    (keys : namesAsRawContext (nameCurrentOwner Y)=namesAsRawContext request.result.directory.oldKey) :
    NativeCreationOwnerContext Y ((meteredSelectedDemand request).bind measureLocalLoad).result :=
  keys.trans (fixed_request_key_context_is_the_actual_charged_successor_context request).symm

#print axioms fixed_request_key_context_is_the_actual_charged_successor_context
#print axioms a_fixed_request_with_literal_owner_keys_fills_the_selected_guard
end
end J6R111KeptOwnerFlow

