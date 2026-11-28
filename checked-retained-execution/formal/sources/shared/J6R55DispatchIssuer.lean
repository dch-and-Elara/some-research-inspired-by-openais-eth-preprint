import J6R55DispatchPaid

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8500000
set_option Elab.async false
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false

/-! The selected source packet's issuer is actually generated, not
read from a supplied child counter. Replacing it does not change the
typed page-key lookup or physical selected carrier. -/
namespace J6R55Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R25PreparedSupply J6R34ChildPath J6R49DFS
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS J6R51Online
open J6R50SourceProducer J6R52Dispatch J6R53Dispatch J6R54Dispatch
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable (R : Replayed X.site w q U)

def usingParentIssuer (shell : PayloadShell R) : PayloadShell R :=
  { shell with issued := increment X.birth.job.identifier }

def usingParentIssuerDirectory (shell : PayloadShell R) (D : DirectorySeed R shell) :
    DirectorySeed R (usingParentIssuer R shell) where
  k1 := D.k1
  k2 := D.k2
  ow := D.ow
  oldKey := D.oldKey
  owners := D.owners
  seats := D.seats
  queries := D.queries
  fallback := D.fallback
  valid := D.valid

def mountedIncrementDemand {raw : List (Word (q+1))} {g : Fin 64}
    (find : FixedPicker R) (cert : FixedCarrier R raw g)
    (shell : PayloadShell R) (directory : DirectorySeed R shell) : Meter (LocalLoad X w) :=
  mountedDemand R find cert (usingParentIssuer R shell) (usingParentIssuerDirectory R shell directory)

theorem dispatcher_actually_increments_issuer {raw : List (Word (q+1))} {g : Fin 64}
    (find : FixedPicker R) (cert : FixedCarrier R raw g)
    (shell : PayloadShell R) (directory : DirectorySeed R shell) :
    let K := mountedIncrementDemand R find cert shell directory
    K.result.event.issued=increment X.birth.job.identifier ∧
      K.result.advance.next.birth.job.identifier=(increment X.birth.job.identifier).result ∧
      paidAcquisition K=(find raw g).steps+cert.val.dispatch.steps+6+4+K.result.sidecarCharge := by
  let K := mountedIncrementDemand R find cert shell directory
  have exact : K.result.event.issued=increment X.birth.job.identifier := rfl
  refine ⟨exact,(loaded_job_label K.result).trans (congrArg Meter.result exact),?_⟩
  exact mounted_demand_exact_purchase R find cert (usingParentIssuer R shell)
    (usingParentIssuerDirectory R shell directory)

#print axioms usingParentIssuerDirectory
#print axioms mountedIncrementDemand
#print axioms dispatcher_actually_increments_issuer
end
end J6R55Dispatch
