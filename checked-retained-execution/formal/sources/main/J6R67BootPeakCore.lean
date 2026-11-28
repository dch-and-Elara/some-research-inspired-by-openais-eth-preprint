import J6R66BootPeakHandoff
import J6R64BootSeatsInstall

/-!
Expose the actual first-scope interpreter behind compact typed projections.
Structural layout parameters remain inside BootOp, so an external request
proof need not reduce the original chart's dependent Call and Ticket.
-/
namespace J6R67.BootPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6ActiveRun J6ActiveSchedule J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R26DescriptorTree J6R36ChildFramedRoute J6R48RawRoute J6R50SourceProducer
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R52CacheWhole J6R48DFS J6R30ProducedGateRegistry
open J6R64.BootSeats J6R66.BootPeak
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

structure BootOp (f : ℤ[X]) (ell key prec tw bw page : ℕ) (Out : Type) where
  s : ℕ
  C : ℕ
  cfg : RootBounds s C f
  sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)
  root : Call (PhysicalHost f ell)
  hf : f.Monic
  source : Prepared cfg sel root hf
  slot : (Plan sel).Slot root
  initial : Meter (StoredSite source ((Path.root : Path sel root root).ticket slot) key prec tw bw page)
  retire : PageJob f ell key prec tw bw page→ℕ
  continuation : (site : StoredSite source ((Path.root : Path sel root root).ticket slot) key prec tw bw page)→
    ResidentBank site→SM (PageBank f ell key prec tw bw page) Out
  fallback : Meter Out

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ} {Out : Type}
variable (A : BootOp f ell key prec tw bw page Out)
variable (B : PageBank f ell key prec tw bw page)

def BootOp.job : PageJob f ell key prec tw bw page := A.initial.result.birth.job

def BootOp.run : Meter (Out×PageBank f ell key prec tw bw page) :=
  bootBankDemand A.initial A.retire A.continuation A.fallback B

def BootOp.inside : Meter (Out×PageBank f ell key prec tw bw page) :=
  let installed := installResidentBank A.initial.result
  A.continuation A.initial.result installed.result (afterOne B A.job)

def BootOp.installFee : ℕ := (installResidentBank A.initial.result).steps

def BootOp.publicationFee : ℕ := publishFee B A.job.entry A.job.offset A.job.built

theorem first_boot_uses_its_actual_child_bank_once (ready : JobsReady B [A.job]) :
    A.run B=⟨((A.inside B).result.1,B),
      A.initial.steps+(A.publicationFee B+(A.installFee+(A.inside B).steps)+A.retire A.job+4)⟩ ∧
    mountedSelectedBits (afterOne B A.job)=mountedSelectedBits B+mountedInsertionBits A.job :=
  ⟨actual_boot_scope_installs_one_addon_bank A.initial A.retire A.continuation A.fallback B ready,
    publication_adds_exact_selected_record B A.job⟩

#print axioms BootOp.run
#print axioms first_boot_uses_its_actual_child_bank_once
end
end J6R67.BootPeak
