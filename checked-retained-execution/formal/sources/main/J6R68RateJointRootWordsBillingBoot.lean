import J6R66ActiveRun
import J6R55CachedLedgerCore

/-! The first callback in R66 is literally this boot-with-header meter.
Its successful own debit is the R55 scope debit, not another publication
and not a fee on a disconnected simulation. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R24MeteredRecursion J6R53PeakAddon J6R55CachedLedger
open J6ActiveRun J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R52CacheWhole J6R48DFS J6R64Active

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4100
set_option maxHeartbeats 8000000
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Here" => (Path.root : Path sel r r)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Slot" => ((Plan sel).Slot r)
local notation "Site" => (fun w : Slot=>StoredSite T ((Here).ticket w) key prec tw bw page)

theorem real_first_install_ok (B : L) (j : J) (ready : JobsReady B [j]) :
    (j.install B).result.2=true := by
  rw [(next_job_exact B j [] ready).1]

theorem r66_first_boot_exact_own_debit (M : OnlineMachine T key prec tw bw page rate)
    (w : Slot) {Out : Type} (retire : J→ℕ)
    (child : (next : Site w)→WithIncoming next Out) (bad : Meter Out) (B : L)
    (legal : ReadyOnStack (borns M) B) :
    let first := M.initial w
    let j := first.result.birth.job
    let mounted := installResidentBank first.result
    let h := real_first_install_ok B j (legal Here w)
    let after := child first.result mounted.result (j.install B).result.1
      (successful_publish_has_exact_head j B h)
    let run := bootWithHeader first retire child bad B
    run.result=(after.result.1,B) ∧
      run.steps=cachedScopeOwn M retire B Here w+after.steps := by
  let first := M.initial w
  let j := first.result.birth.job
  let h := real_first_install_ok B j (legal Here w)
  have fee : (j.install B).steps=publishFee B j.entry j.offset j.built :=
    congrArg Meter.steps (next_job_exact B j [] (legal Here w)).1
  dsimp only [bootWithHeader,withScopeHeader]
  rw [dif_pos h]
  refine ⟨rfl,?_⟩
  change first.steps+((j.install B).steps+
    ((installResidentBank first.result).steps+_)+retire j+4)=_
  rw [fee]
  change _=first.steps+(installResidentBank first.result).steps+
    (publishFee B j.entry j.offset j.built+retire j+4)+_
  ac_rfl

#print axioms real_first_install_ok
#print axioms r66_first_boot_exact_own_debit
end
end J6R68RateJoint.RootWords

