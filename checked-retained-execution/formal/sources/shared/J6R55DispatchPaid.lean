import J6R54DispatchFixedBank
import J6R54DispatchFixedFields
import J6R51OnlineVisitDefs

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8500000
set_option Elab.async false
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false

/-! Reconcile the physical fixed-chart loader with the exact online
demand ABI used inside the mounted public jobs. Search is accounted at
the demand, never by calling the raw cursor a second time. -/
namespace J6R55Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R17ModeTape J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R25PreparedSupply J6R34ChildPath J6R49DFS
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS J6R51Online
open J6R49SourceLayout J6R50SourceProducer J6R52Dispatch J6R53Dispatch J6R54Dispatch
open J6R32StatefulArithmetic J6R32ChildResidentTransfer J6R51Dispatch J6R16ModeCost
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
local notation "Bank" => PageBank f ell key prec tw bw page
local notation "Job" => PageJob f ell key prec tw bw page

/-- Incorporate the performed search and the four-unit exit of the
explicit reader into the original `LocalLoad` meter. The input is
the measured acquisition and not an arbitrary fee for a decoded slot. -/
def forDemand (lookup : ℕ) (K : Meter (LocalLoad X w)) : Meter (LocalLoad X w) :=
  ⟨K.result,lookup+K.steps+4⟩

theorem callback_and_loader_charge_same {Y : Type}
    (lookup : ℕ) (K : Meter (LocalLoad X w))
    (retire : Job→ℕ)
    (child : StoredSite T (J6R48RawRoute.successorTicket v w) key prec tw bw page→SM Bank Y)
    (fallback : Meter Y) (bank : Bank) :
    project (openDemand (forDemand lookup K) retire child fallback bank)=
      attachReply lookup (openDemand K retire child fallback bank) := by
  unfold project attachReply openDemand paidAcquisition forDemand
  dsimp only
  congr 1
  omega

variable (R : Replayed X.site w q U)
variable {raw : List (Word (q+1))} {g : Fin 64}

def mountedDemand (find : FixedPicker R) (cert : FixedCarrier R raw g)
    (shell : PayloadShell R) (directory : DirectorySeed R shell) : Meter (LocalLoad X w) :=
  forDemand (find raw g).steps (cert.val.load shell directory)

theorem mounted_demand_uses_literal_issuer
    (find : FixedPicker R) (cert : FixedCarrier R raw g)
    (shell : PayloadShell R) (directory : DirectorySeed R shell)
    (issued : shell.issued=increment X.birth.job.identifier) :
    (mountedDemand R find cert shell directory).result.event.issued=increment X.birth.job.identifier := by
  exact issued

theorem mounted_demand_exact_purchase
    (find : FixedPicker R) (cert : FixedCarrier R raw g)
    (shell : PayloadShell R) (directory : DirectorySeed R shell) :
    let K := mountedDemand R find cert shell directory
    paidAcquisition K=(find raw g).steps+cert.val.dispatch.steps+6+4+K.result.sidecarCharge := by
  dsimp only [paidAcquisition,mountedDemand,forDemand,RawFields.load,acceptLocalLoad]
  omega

theorem observed_route_is_actual_demand_meter {Y : Type}
    (find : FixedPicker R) (cert : FixedCarrier R raw g) (picked : (find raw g).result=some cert)
    (shell : PayloadShell R) (directory : DirectorySeed R shell)
    (retire : Job→ℕ)
    (child : StoredSite T (J6R48RawRoute.successorTicket v w) key prec tw bw page→SM Bank Y)
    (fallback : Meter Y) (bank : Bank) (other : List (Word (q+1))→Fin 64→Meter Y) :
    fixedRoutedRead R find shell directory retire child fallback bank other raw g=
      project (openDemand (mountedDemand R find cert shell directory) retire child fallback bank) := by
  have h := callback_and_loader_charge_same (X:=X) (w:=w) (find raw g).steps
    (cert.val.load shell directory) retire child fallback bank
  unfold fixedRoutedRead
  dsimp only
  rw [picked]
  exact h.symm

#print axioms callback_and_loader_charge_same
#print axioms mounted_demand_uses_literal_issuer
#print axioms mounted_demand_exact_purchase
#print axioms observed_route_is_actual_demand_meter
end
end J6R55Dispatch
