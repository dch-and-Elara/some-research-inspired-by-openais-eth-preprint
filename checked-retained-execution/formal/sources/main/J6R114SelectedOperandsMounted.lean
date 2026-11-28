import J6R55PublicDemand
import J6R54DispatchFixedBank

/-! Real mounted descendant lookup into the original FixedRequest ABI.
A nonempty exact position is a property of the held table, not a
supplied arbitrary option or fixed-picker function. -/
namespace J6R114SelectedOperands
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J1PPrinted J6R24MeteredRecursion J6R26DescriptorTree J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R50SourceProducer J6R51Online
open J6R52Dispatch J6R53Dispatch J6R54Dispatch J6R55Public J6R55Dispatch
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4400
set_option maxHeartbeats 7000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}
variable (Y : StoredSite T v key prec tw bw page) (w : (Plan sel).Slot v.child)

/-- Physical operands for this one addressed request. The exact hit
is an existential proof about the actual mounted bytes; it is not
a second execution of the lookup and adds no callable directory. -/
structure MountedRequestAt where
  q : ℕ
  emitted : ExplicitSelectedWords Y.site w q
  replay : Replayed Y.site w q emitted
  raw : List (Word (q+1))
  group : Fin 64
  bins : MountedFixedRows replay
  orderedHit :
    ∃ (car : FixedCarrier replay raw group)
      (before after : List (Σ row : List (Word (q+1)), FixedCarrier replay row group)),
      (bins group).result=before++⟨raw,car⟩::after ∧
      ∀ E∈before,E.1≠raw
  shell : PayloadShell replay
  directory : DirectorySeed replay shell

theorem chosen_bin_has_the_actual_request (D : MountedRequestAt Y w) :
    (chooseMountedFixed D.replay D.bins D.raw D.group).result.isSome := by
  obtain ⟨car,before,after,held,first⟩ := D.orderedHit
  rw [mounted_fixed_reader_paid_and_exact D.replay D.bins D.raw D.group car before after held first]
  rfl

variable {Y w}
variable (source : Meter (MountedRequestAt Y w))

/-- Acquire the measured shell/chart operands once on this site.
The original R54 picker runs only when meteredSelectedDemand asks
for its raw word. Its own cost, including bins.read, stays there. -/
def addressedRequestFromActualMountedSource : Meter (FixedRequest Y w) :=
  let D := source.result
  ⟨⟨D.q,D.emitted,D.replay,D.raw,D.group,chooseMountedFixed D.replay D.bins,
    chosen_bin_has_the_actual_request Y w D,D.shell,D.directory⟩,source.steps+4⟩

theorem request_packet_keeps_exact_source_and_only_its_assembly_charge :
    let req := addressedRequestFromActualMountedSource source
    let D := source.result
    req.steps=source.steps+4 ∧ req.result.find=chooseMountedFixed D.replay D.bins := ⟨rfl,rfl⟩

theorem original_demand_reads_the_actual_bin_once :
    let req := addressedRequestFromActualMountedSource source
    let D := source.result
    let read := chooseMountedFixed D.replay D.bins D.raw D.group
    let picked := read.result.get (chosen_bin_has_the_actual_request Y w D)
    let openCost := forDemand read.steps (picked.val.load (J6R55Dispatch.usingParentIssuer D.replay D.shell)
      (J6R55Dispatch.usingParentIssuerDirectory D.replay D.shell D.directory))
    meteredSelectedDemand req = ⟨openCost.result,(source.steps+4)+openCost.steps+3⟩ := rfl

#print axioms chosen_bin_has_the_actual_request
#print axioms addressedRequestFromActualMountedSource
#print axioms request_packet_keeps_exact_source_and_only_its_assembly_charge
#print axioms original_demand_reads_the_actual_bin_once
end
end J6R114SelectedOperands

