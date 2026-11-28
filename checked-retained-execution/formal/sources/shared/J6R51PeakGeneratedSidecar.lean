
import J6R51PeakSidecar
import J6R50SourceProducerInstaller

/-! The same source operation emits and installs this concrete sidecar.
The separate sidecar fee is not part of the already-counted immutable
page publication. Count the two selected tapes only when this
installation is performed, not on arbitrary runtime callbacks. -/
namespace J6R51Peak
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun J6R48GeneratedAddons J6R50SourceProducer

open J6R48RawRoute

set_option autoImplicit false
set_option maxHeartbeats 12500000
set_option maxRecDepth 3500

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (X : StoredSite T v key prec tw bw page)
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable {H : Replayed X.site w q U}
variable (W : NativeEventOnly H) (D : LocalDirectory X W)

theorem actual_generated_sidecar_selected_bits_and_fee :
    let next := (prepareOnlineAdvance X W D).next
    let B := next.birth
    let S := next.site
    let made := emit (D.read X W) B.native.physical.order
    S.install.result=some S.bank ∧
    made.result=S.input ∧
    (pairedAddonPayload S).length≤
      (2*v.child.edges)*(B.port+2*addonCap D.ow (dim (successorTicket v w)) key prec page) ∧
    made.steps+S.install.steps=8+
      (B.native.physical.order.map (fun h=>((D.read X W) h).steps+
        addonFee D.ow (dim (successorTicket v w)) key prec page
          ((D.read X W) h).result.oldOrigin.pageKey.isSome+4)).sum+
      (made.result.map (fun x=>3*B.port+11+
        addonFee D.ow (dim (successorTicket v w)) key prec page
          x.oldOrigin.pageKey.isSome)).sum := by
  let next := (prepareOnlineAdvance X W D).next
  have S := next.site.install_exact
  have fee := actual_generated_sidecar_has_measured_read_cost X W D
  exact ⟨S.1.trans (congrArg some next.site.bank_exact.symm),
    rfl,true_sidecar_install_fields_bound next.site,fee.2⟩

#print axioms actual_generated_sidecar_selected_bits_and_fee
end J6R51Peak
