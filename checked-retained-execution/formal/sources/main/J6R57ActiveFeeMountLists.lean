import J6R55CachedLedgerCore
import J6R52PeakCachedStack

/-! Expose the physical terms priced by the R56 cache mount:
one available parent port tape, one actual resident table, and the
half-order of the selected child. This is not a new scope's debit. -/
namespace J6R57ActiveFee
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R51ParentFrames J6R52CacheWhole J6R52Peak J6R55CachedLedger

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 2750
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

theorem actual_descendant_mount_reads_named_lists
    (M : OnlineMachine T key prec tw bw page q)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c) :
    let X := sourceState M p w
    let B := (installResidentBank X).result
    let D := X.birth.native.physical
    cacheMountFee M (Path.step p w) ≤ 16+(D.raw.map rowScanFee).sum+
        ((halfOrder T (p.ticket w) D).map (fun h=>visitFee X.birth.port X.site.ownerWidth
          (J6R36ChildFramedRoute.dim (p.ticket w)) key prec page B.rows.length
          (D.record h.val).body.length (X.site.aux h.val).oldOrigin.pageKey.isSome)).sum := by
  let X := sourceState M p w
  let B := (installResidentBank X).result
  let D := X.birth.native.physical
  let scan := (D.raw.map rowScanFee).sum
  let loads := ((halfOrder T (p.ticket w) D).map (fun h=>visitFee X.birth.port X.site.ownerWidth
    (J6R36ChildFramedRoute.dim (p.ticket w)) key prec page B.rows.length
    (D.record h.val).body.length (X.site.aux h.val).oldOrigin.pageKey.isSome)).sum
  have localFee : (paidParentFrames X.site B.rows).steps ≤ 11+scan+loads :=
    paid_parent_frames_local_cap X.site B.rows B.exactRows
  change (sourceMounted (M:=M) p w).steps ≤ 16+scan+loads
  rw [(actual_active_mount_has_exact_typed_rows_and_fee M p w).1]
  change (paidParentFrames X.site B.rows).steps+3+2 ≤ 16+scan+loads
  omega

#print axioms actual_descendant_mount_reads_named_lists
end
end J6R57ActiveFee
