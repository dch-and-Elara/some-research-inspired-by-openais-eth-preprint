import J6R55CachedLedgerCore

/-! Preparation fees cannot be inferred from shape or correctness
alone: the actual source's supplied Meter can carry arbitrarily large
prepaid work with the very same prepared machine. -/
namespace J6R57ActiveFee
open scoped Polynomial
open Polynomial AOracleMachineTime
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R51Online

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
set_option maxRecDepth 2500
set_option Elab.async false

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

def padOnlyActivePreparation
    (M : OnlineMachine T key prec tw bw page q) (extra : ℕ) :
    OnlineMachine T key prec tw bw page q :=
  { M with
    activeRoot := fun a=>let A := M.activeRoot a; ⟨A.result,A.steps+extra⟩
    activeAfter := fun p u X a=>let A := M.activeAfter p u X a; ⟨A.result,A.steps+extra⟩ }

theorem actual_prepared_root_value_does_not_cap_its_fee
    (M : OnlineMachine T key prec tw bw page q)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<r.edges) (cap : ℕ) :
    ∃ W : OnlineMachine T key prec tw bw page q,
      let p : Path sel r r := .root
      (preparedActive W p a).result=(preparedActive M p a).result ∧ cap<(preparedActive W p a).steps := by
  refine ⟨padOnlyActivePreparation M (cap+1),rfl,?_⟩
  change cap < (M.activeRoot a).steps+(cap+1)
  omega

#print axioms actual_prepared_root_value_does_not_cap_its_fee
end J6R57ActiveFee
