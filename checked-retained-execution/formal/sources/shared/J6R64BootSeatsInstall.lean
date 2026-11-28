import J6R64BootSeatsAssembly
import J6R52CacheWholePrep

/-! Successful cached first-scope accounting. The actual boot Meter
and the installed child addon bank each enter once. The outer live
exterior PageBank is supplied, not reconstructed. -/
namespace J6R64.BootSeats
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R15ModeCost
open J6ActiveRun J6ActiveSchedule J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R26DescriptorTree J6R36ChildFramedRoute J6R48RawRoute J6R50SourceProducer
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R52CacheWhole J6R48DFS J6R30ProducedGateRegistry
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000
set_option maxRecDepth 4500
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {w : (Plan sel).Slot r} {Out : Type}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Site" => (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page)

theorem actual_boot_scope_installs_one_addon_bank
    (boot : Meter Site) (retire : J→ℕ)
    (child : (st : Site)→ResidentBank st→SM L Out)
    (fallback : Meter Out) (B : L) (legal : JobsReady B [boot.result.birth.job]) :
    let j := boot.result.birth.job
    let installed := installResidentBank boot.result
    let next := child boot.result installed.result (afterOne B j)
    bootBankDemand boot retire child fallback B=
      ⟨(next.result.1,B),boot.steps+
        (publishFee B j.entry j.offset j.built+(installed.steps+next.steps)+retire j+4)⟩ := by
  unfold bootBankDemand
  dsimp only
  rw [J6R48DFS.paid_scope_exact _ _ _ _ _ legal]

#print axioms actual_boot_scope_installs_one_addon_bank
end
end J6R64.BootSeats
