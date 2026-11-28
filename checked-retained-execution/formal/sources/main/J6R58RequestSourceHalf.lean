import J6R58RequestSourceDirectory
import J6R58RequestSourceHalfBits

/-! Decode the one appended side bit from the actual R48 physical
port address. The raw record acquisition remains a measured input;
there is no given ancestor edge-key or side value. -/
namespace J6R58RequestSource
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open P11FullPacking J6R9PacketScopes J6R10Repack J6R12CollisionEdges
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R33GeneratedChildSite
open J6R34ChildPath J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R50SourceProducer J6R51Online J6R52Dispatch
open J6R21Ancestor J6R36ChildFramedRoute J6R34RootAtlas J6R20Ancestor
open J6R51ParentFrames J6R52CacheSource J6R53OldOwner J6R25PreparedSupply
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16800000
set_option maxRecDepth 4200
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
variable {u : (Plan sel).Slot v.child} {q : ℕ} {U : ExplicitSelectedWords X.site u q}
variable (R : Replayed X.site u q U)
local notation "Edge" => v.child.host.Edge
local notation "Key" => (childKey T v X.birth.native.physical)

theorem exactly_selected_native_half_address (h : Port Edge) :
    ((selectedAdjacent R).generated.result.record h).address=childHalfKey (Key (edge h)) (side h) := by
  let d := ticketReady T (successorTicket v u)
  let t := Ticket.centerAt (successorTicket v u)
  let H := selectedAdjacent R
  exact (physically_generated_child_keeps_route X.site d t H.code H.raw H.exact h).2.2.1

structure PaidSelectedRead where
  read : Port Edge→Meter (PortRow (X.birth.port+1))
  literal : ∀ h,(read h).result=(selectedAdjacent R).generated.result.record h

variable (P : PaidSelectedRead X R)

def queryFromActualHalf (h : Port Edge) : Meter (Word X.birth.port × Bool) :=
  let Q := P.read h
  let D := splitChildBits X.birth.port Q.result.address.bits
  let actual := (P.literal h)
  have decoded : D.result=some (Key (edge h),side h) := by
    unfold D Q
    rw [actual,exactly_selected_native_half_address X R h,measured_decoder_strips_exact_ancestor_address]
  let out := unwrapSuccess D (by rw [decoded]; rfl)
  ⟨out.result,Q.steps+out.steps+3⟩

theorem actual_half_lookup_exact_and_paid (h : Port Edge) :
    queryFromActualHalf X R P h=
      ⟨(Key (edge h),side h),(P.read h).steps+5*X.birth.port+7⟩ := by
  let Q := P.read h
  let D := splitChildBits X.birth.port Q.result.address.bits
  have fee : D=⟨some (Key (edge h),side h),5*X.birth.port+4⟩ := by
    unfold D Q
    rw [P.literal h,exactly_selected_native_half_address X R h,
      measured_decoder_strips_exact_ancestor_address]
  have q (hD : D.result.isSome) : unwrapSuccess D hD=⟨(Key (edge h),side h),D.steps⟩ :=
    unwrap_success_exact D hD _ (congrArg Meter.result fee)
  unfold queryFromActualHalf
  dsimp only
  rw [q,congrArg Meter.steps fee]
  congr 1

def indexFromSelectedHalf : PaidPortIndex X :=
  ⟨queryFromActualHalf X R P,fun h=>congrArg Meter.result (actual_half_lookup_exact_and_paid X R P h)⟩

#print axioms exactly_selected_native_half_address
#print axioms actual_half_lookup_exact_and_paid
#print axioms indexFromSelectedHalf
end
end J6R58RequestSource
