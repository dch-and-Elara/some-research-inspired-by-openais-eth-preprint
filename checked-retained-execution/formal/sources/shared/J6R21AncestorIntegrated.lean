import J6R21AncestorProgram
import J6R21AncestorWholeEnvelope
import J6R21AncestorOriginReads

/-! Same prepared leaf tape family for semantics and the priced ledger.
The residual entry bill is the exact sum of the invoked programs,
including the two source-specific query adapters, not an asserted
uniform fee for a callback. Bootstrap, active combine, and root output
conversion are distinct, not covered by this receipt. -/
namespace J6R21Ancestor
open scoped BigOperators Polynomial Classical
open J6ActiveRun J6R10Reachable J6R12Blueprint J6R11Blueprint J1PPrinted
open J6R16ModeCost J6R17ModeTape

variable {f : ℤ[X]} {ell s C : ℕ} (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic)
variable [DecidableEq (Envelope (N sel) (Childs sel) r)]

theorem verified_source_on_prepared_tapes (L : NativeLeafTapes sel r hf)
    (hr : Stable s C r) (d0 : r.depth=0) (p0 : r.prec≤C*s)
    (modeInputs : LayoutSupply (C:=C) sel r) :
    let H := pathLimit s C
    let T := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
    let mode := ∑ j∈Finset.range H,((occurrences (Plan sel) r j).map
      (builtCallCost cfg sel hr d0 p0 modeInputs)).sum
    let leaves := totalLeafComponent sel r hf L (fun _ D=>D.run.steps) H
    let billed := totalLeafComponent sel r hf L (fun _ D=>D.directBill) H
    (paidSource sel r hf L).run r=(sourceBlueprint sel r hf).program.run r ∧
    mode+leaves≤billed+
      (H*comboFee s C+(H+1)*uniformLeafArithmetic (C:=C) (s:=s) r)*2^(prefixConstant C*T) := by
  exact ⟨paid_source_root sel r hf L,whole_mode_and_leaf_upper cfg sel r hf L hr d0 p0 modeInputs⟩

#print axioms verified_source_on_prepared_tapes
end J6R21Ancestor

