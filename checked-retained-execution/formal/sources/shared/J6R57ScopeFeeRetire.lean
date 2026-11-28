import J6R48DFSScope
import J6R27OriginalGateModeCompare

/-! One concrete, explicit retirement policy for the visible pair of
persistent registry list-tail handles. This charges the bits of the
two fixed-width handle copies. It is not a garbage-collector or
heap-reclamation contract. -/
namespace J6R57ScopeFee
open AOracleMachineTime J6R15ModeCost J6R27OriginalGate
open J6R48DFS J6R30ProducedGateRegistry J6R32StatefulArithmetic
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

structure SavedDirectoryTails (width : ℕ) where
  headers : Word width
  records : Word width

def restoreSavedDirectory {width : ℕ} (x : SavedDirectoryTails width) :
    Meter (SavedDirectoryTails width) :=
  let h := copyFixed x.headers
  let r := copyFixed x.records
  ⟨⟨h.result,r.result⟩,h.steps+r.steps+6⟩

def twoTailFee (width : ℕ) : ℕ := 6*width+8

theorem restored_directory_handles_exact {width : ℕ} (x : SavedDirectoryTails width) :
    restoreSavedDirectory x=⟨x,twoTailFee width⟩ := by
  cases x with
  | mk h r =>
    simp only [restoreSavedDirectory,copy_fixed_exact,twoTailFee]
    congr 1
    omega

def retireSavedDirectory {width key prec tw bw : ℕ} {D : Type*}
    (tails : SavedDirectoryTails width) (_ : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D) : ℕ :=
  (restoreSavedDirectory tails).steps

theorem retire_debit_is_the_fixed_handle_fee {width key prec tw bw : ℕ} {D : Type*}
    (tails : SavedDirectoryTails width) (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D) :
    retireSavedDirectory tails j=twoTailFee width :=
  congrArg Meter.steps (restored_directory_handles_exact tails)

theorem actual_scope_with_explicit_return_debit {width key prec tw bw : ℕ} {D A : Type*}
    (tails : SavedDirectoryTails width)
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : SM (Ledger key prec tw bw D) A) (fallback : Meter A)
    (B : Ledger key prec tw bw D) (ready : JobsReady B [j]) :
    withScope (retireSavedDirectory tails) j go fallback B=
      ⟨((go (afterOne B j)).result.1,B),
        publishFee B j.entry j.offset j.built+(go (afterOne B j)).steps+twoTailFee width+4⟩ := by
  rw [paid_scope_exact _ _ _ _ _ ready,retire_debit_is_the_fixed_handle_fee]

#print axioms restored_directory_handles_exact
#print axioms retire_debit_is_the_fixed_handle_fee
#print axioms actual_scope_with_explicit_return_debit
end J6R57ScopeFee
