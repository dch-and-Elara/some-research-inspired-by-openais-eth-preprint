
import J6R34RootAtlasOccurrence
import J6R48DFSIssued

/-! Discharge the whole-family atlas census using the original R34
compiled births, with the same occurrence and page payloads. Only
the already-proved dependent equality of page address word widths is
transported. No frame or atlas is constructed by the observer. -/
namespace J6R50Peak
open scoped Polynomial
open AOracleMachineTime A1R12
open J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R33GeneratedChildSite J6R34RootAtlas J6R48DFS

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 19500000

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {ticket : Ticket sel r}

theorem width_transport_keeps_atlas_count {a b : ℕ} (eq : a=b)
    (B : Birth T ticket key prec tw bw a) :
    let new : Birth T ticket key prec tw bw b := eq ▸ B
    new.job.immutable.payload.payload.pages.length=B.job.immutable.payload.payload.pages.length := by
  cases eq
  rfl

theorem actual_compiled_occurrence_census (X : OccurrenceInput T ticket key prec tw bw page) :
    (compileOccurrence X).job.immutable.payload.payload.pages.length=Nat.card ticket.child.host.Col := by
  let receipt := Classical.choice (occurrence_real_receipt X)
  let issued := padCost X.issued (X.native.steps+X.physical.steps+X.words.steps+4)
  let b := issuedBirth X.native.result issued X.words.result X.hOld receipt
  change ((X.width ▸ b : Birth T ticket key prec tw bw page)).job.immutable.payload.payload.pages.length=_
  exact (width_transport_keeps_atlas_count X.width b).trans
    (issued_atlas_counts_real_pages X.native.result issued X.words.result X.hOld receipt)

theorem actual_compiled_family_census (I : InputFamily T key prec tw bw page) :
    AllExactPages (compileFamily I) := by
  intro c p w
  exact actual_compiled_occurrence_census (I p w)

#print axioms width_transport_keeps_atlas_count
#print axioms actual_compiled_occurrence_census
#print axioms actual_compiled_family_census
end J6R50Peak
