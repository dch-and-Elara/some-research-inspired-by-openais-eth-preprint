import J6R68RateJointRootWordsBilling

/-! Specialization to the actual R66 root reader at one printed address:
the child is `runAfter` and the fallback is the original zero register,
not a generic replacement continuation. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R26DescriptorTree J6R21Ancestor
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R24MeteredRecursion J6R55CachedLedger
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R22Active J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R52CacheWhole J6R48DFS J6R64Active J6R66Active
open J6R57ScopeFee J6R67UnifiedRate J6R49DFS J6R62ActivePrep

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4250
set_option maxHeartbeats 8900000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page rate cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Here" => (Path.root : Path sel r r)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "Machine" => (OnlineMachine T key prec tw bw page rate)

theorem actual_r66_native_first_reader_bound (M : Machine)
    (F : RetainedAfter T key prec tw bw page rate cw)
    (B : L) (safe : ReadyOnStack (borns M) B) (score : MeasuredScopeInputs M B)
    {pointerWidth : ℕ} (tails : SavedDirectoryTails pointerWidth)
    (a : (S).cutoff<r.edges) (t : Center S r) (z : Probe S r)
    (β : NativeMenu (N sel) r t) (g : Fin 64) :
    let d := readyAtPath T Here a
    let w := addressed (sel:=sel) d t z β g
    let first := M.initial w
    let j := first.result.birth.job
    let child := J6R66Active.runAfter M F (retireSavedDirectory tails) r Here w
    let bad : Meter (Block (T.bank (registerPrecision S r t) (register_positive d t)) ell) := zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp
    let spent := bootWithHeader first (retireSavedDirectory tails) child bad B
    let h := real_first_install_ok B j (safe Here w)
    let ret := child first.result (installResidentBank first.result).result (j.install B).result.1
      (successful_publish_has_exact_head j B h)
    spent.result.2=B ∧ spent.steps≤measuredPerScope score pointerWidth+ret.steps := by
  let d := readyAtPath T Here a
  let w := addressed (sel:=sel) d t z β g
  let child := J6R66Active.runAfter M F (retireSavedDirectory tails) r Here w
  let bad : Meter (Block (T.bank (registerPrecision S r t) (register_positive d t)) ell) := zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp
  have h := counted_r66_first_boot_uses_scope_bound (M:=M) w tails child bad B safe score
  exact ⟨congrArg Prod.snd h.1,h.2⟩

#print axioms actual_r66_native_first_reader_bound
end
end J6R68RateJoint.RootWords

