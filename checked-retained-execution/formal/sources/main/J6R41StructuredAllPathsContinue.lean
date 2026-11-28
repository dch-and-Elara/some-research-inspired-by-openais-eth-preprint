import J6R41StructuredAllPathsLocal
import J6R37StructuredRootChain

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000
set_option maxRecDepth 2800

/-! Start at the exact real native sidecar lane, then keep its body
and stamp through a typed trace of retentions. Individual subsequent
raw inputs must still take this carried value (the trace alone does
not force an unconstrained physical input's bytes). -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R20Ancestor J6R37StructuredRoot

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)

def NativeRoute (k : PageAt T v) {cur : Point f ell}
    (tr : Trace (bornPoint T v k) cur) (x : PortAt cur) : Prop :=
  let h := edge (tr.back x).val
  let lane := S.issuedLane h true
  S.inWrite (S.frame h) ∧
    (carryBody tr.depth lane.body).result=tr.literal (originSeed (layout T v) (axis T v) v.groupAt k) x ∧
    lane.origin=nativeOrigin S k ∧ lane.origin.stamp.created.val=(entry cur).created

theorem native_seed_retention_trace (k : PageAt T v) {cur : Point f ell}
    (tr : Trace (bornPoint T v k) cur) (x : PortAt cur) :
    NativeRoute S k tr x := by
  obtain ⟨written,body,claim,tag⟩ := native_page_body_at_issue S k (tr.back x) Q.native.gWord
  refine ⟨written,?_,claim,tag.trans tr.tag.symm⟩
  dsimp only
  rw [body,carry_body_exact,tr.literal_exact]

#print axioms native_seed_retention_trace
end J6R41StructuredAllPaths