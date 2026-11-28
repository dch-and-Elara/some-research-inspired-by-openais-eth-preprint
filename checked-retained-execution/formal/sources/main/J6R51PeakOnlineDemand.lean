
import J6R51PeakNativeVisit
import J6R51PeakGeneratedSidecar
import J6R51OnlineCore

/-! One measured online request consumes exactly the observed produced
header and sidecar, mounts the existing page compiler result, and
gives that same StoredSite and scope to the continuation. Selected
working widths do not redefine the original operation's meter. -/
namespace J6R51Peak
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R34ChildPath
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R51Online J6R36ChildFramedRoute

open J6R48RawRoute

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 17500000

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

theorem exact_online_demand_with_local_payloads {A : Type}
    (start : Meter (LocalLoad X w)) (retire : J→ℕ)
    (child : StoredSite T (successorTicket v w) key prec tw bw page→SM L A)
    (fallback : Meter A) (registry : L) (sync : registry.synced)
    (fresh : ∀ h∈registry.headers,h.id≠start.result.event.issued.result)
    (U : ℕ) (resident : ∀ h∈registry.headers,h.bytes.length≤U)
    (current : start.result.advance.next.birth.job.entry.result.bytes.length≤U) :
    let K := start.result
    let next := K.advance.next
    let B := next.birth
    let j := B.job
    let run := openDemand start retire child fallback registry
    let out := child next (afterOne registry j)
    run=⟨(out.result.1,registry),paidAcquisition start+
      (publishFee registry j.entry j.offset
        ⟨some ⟨B.shape,B.rows⟩,B.compilePages.steps+shapeFrameFee prec⟩+
        out.steps+retire j+4)⟩ ∧
    directoryBits (j.install registry).result.1=directoryBits registry+insertionBits j ∧
    (∀ b∈selectedInstallSnapshots j.entry registry.headers,b.length≤2*key+3*U+1) ∧
    (chosenParseFields j).length≤2*key+3*U+prec ∧
    (pairedAddonPayload next.site).length≤
      (2*v.child.edges)*(B.port+2*addonCap K.directory.ow (dim (successorTicket v w)) key prec page) := by
  let K := start.result
  let B := K.advance.next.birth
  let j := B.job
  have newId : ∀ h∈registry.headers,h.id≠j.identifier := by
    rw [show j.identifier=K.event.issued.result from loaded_job_label K]
    exact fresh
  have op := paid_job_mounts_the_same_selected_directory registry j sync newId
  have bill := open_demand_exact start retire child fallback registry sync fresh
  dsimp only at bill
  change openDemand start retire child fallback registry=⟨
    ((child K.advance.next (j.install registry).result.1).result.1,registry),
    paidAcquisition start+(publishFee registry j.entry j.offset
        ⟨some ⟨B.shape,B.rows⟩,B.compilePages.steps+shapeFrameFee prec⟩+
      (child K.advance.next (j.install registry).result.1).steps+retire j+4)⟩ at bill
  rw [op.1] at bill
  refine ⟨bill,op.2,fun b mem=>actual_fresh_install_temporary_bits j.entry registry.headers
    newId resident current b mem,?_,?_⟩
  · rw [(readback_precision_fields_exact j).1]
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 3 current) _) _
  · exact (actual_generated_sidecar_selected_bits_and_fee X K.event K.directory).2.2.1

#print axioms exact_online_demand_with_local_payloads
end J6R51Peak
