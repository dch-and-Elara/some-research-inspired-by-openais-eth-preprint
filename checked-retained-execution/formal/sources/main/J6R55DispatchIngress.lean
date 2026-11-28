import J6R55DispatchIssuer

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

/-! This is the actual demand computation for one mounted slot. A
proof that a row is present is used only to unwrap the Option from the
paid binary search. There is no separate supplied selected event. -/
def readMountedInput
    (bins : MountedFixedRows R) (raw : List (Word (q+1))) (g : Fin 64)
    (shell : PayloadShell R) (D : DirectorySeed R shell)
    (existsRow : (chooseMountedFixed R bins raw g).result.isSome) : Meter (LocalLoad X w) :=
  let hit := chooseMountedFixed R bins raw g
  let B := hit.result.get existsRow
  forDemand hit.steps (B.val.load (usingParentIssuer R shell) (usingParentIssuerDirectory R shell D))

theorem read_mounted_input_is_selected
    (bins : MountedFixedRows R) (raw : List (Word (q+1))) (g : Fin 64)
    (shell : PayloadShell R) (D : DirectorySeed R shell)
    (existsRow : (chooseMountedFixed R bins raw g).result.isSome) (cert : FixedCarrier R raw g)
    (picked : (chooseMountedFixed R bins raw g).result=some cert) :
    readMountedInput R bins raw g shell D existsRow=
      mountedIncrementDemand R (chooseMountedFixed R bins) cert shell D := by
  have eq : (chooseMountedFixed R bins raw g).result.get existsRow=cert := Option.get_of_eq_some _ picked
  unfold readMountedInput
  dsimp only
  rw [eq]
  rfl

theorem mounted_input_increment_acquisition_receipt
    (bins : MountedFixedRows R) (raw : List (Word (q+1))) (g : Fin 64)
    (shell : PayloadShell R) (D : DirectorySeed R shell)
    (existsRow : (chooseMountedFixed R bins raw g).result.isSome) :
    let K := readMountedInput R bins raw g shell D existsRow
    let cert := (chooseMountedFixed R bins raw g).result.get existsRow
    K.result.event.issued=increment X.birth.job.identifier ∧
      K.result.advance.next.birth.job.identifier=(increment X.birth.job.identifier).result ∧
      paidAcquisition K=(chooseMountedFixed R bins raw g).steps+cert.val.dispatch.steps+
        6+4+K.result.sidecarCharge := by
  exact dispatcher_actually_increments_issuer R (chooseMountedFixed R bins)
    ((chooseMountedFixed R bins raw g).result.get existsRow) shell D

#print axioms readMountedInput
#print axioms read_mounted_input_is_selected
#print axioms mounted_input_increment_acquisition_receipt
end
end J6R55Dispatch
