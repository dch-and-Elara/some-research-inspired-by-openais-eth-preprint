import J6R94HeldOwnerProviderRetainRoster
import J6R102NativeCodeMeterDemand

/-! The original measured native-code select is executed once on
a retained physical load. Neither the native route nor the complete
owner roster is rebuilt merely to choose an ordinal width. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R27OriginalGate
open J6R26DescriptorTree J6R34ChildPath J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R50SourceProducer J6R51Online J6R53OldOwner J6R59Public J6R94HeldOwnerProvider J6R102NativeCodeMeter
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 4700
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page gate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (Y : StoredSite T v key prec tw bw page)
variable {u : (Plan sel).Slot v.child}
variable (gates : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gate)))
variable (K : Meter (HeldOwnerLoad Y (u:=u) gates))

def retainedWithMeasuredCode : Meter (HeldOwnerLoad Y (u:=u) gates) :=
  let code := measureLocalLoad K.result.load
  ⟨⟨code.result,K.result.held⟩,K.steps+code.steps⟩

theorem retained_native_code_is_paid_once_and_keeps_the_entire_roster :
    let prep := retainedWithMeasuredCode Y gates K
    let older : Meter (LocalLoad Y u) := ⟨K.result.load,K.steps⟩
    (⟨prep.result.load,prep.steps⟩ : Meter (LocalLoad Y u))=older.bind measureLocalLoad ∧
      prep.result.held=K.result.held := ⟨rfl,rfl⟩

theorem retained_native_code_does_not_change_the_owner_key_context
    (law : NativeCreationOwnerContext Y K.result.load) :
    NativeCreationOwnerContext Y (retainedWithMeasuredCode Y gates K).result.load := by
  unfold NativeCreationOwnerContext at law ⊢
  rw [actual_next_owner_context_is_the_emitted_directory] at law ⊢
  exact law

#print axioms retained_native_code_is_paid_once_and_keeps_the_entire_roster
#print axioms retained_native_code_does_not_change_the_owner_key_context
end
end J6R111KeptOwnerFlow

