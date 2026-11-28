import J6R55PublicDemand

/-! The arithmetic operator record has no old initial loader and no
old demand callback. Both acquisition functions of the actual R51
machine are filled with the measured objects which will be consumed. -/
namespace J6R55Public
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6ActiveRun J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R48DFS J6R49DFS
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
set_option maxRecDepth 3550
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

structure OnlineOperators (T : Prepared cfg sel root hf) (key prec tw bw page rate : ℕ) where
  modeWidth : 0<rate
  activeRoot : ∀ h : (S).cutoff<root.edges,
    Meter (ActiveMachine sel (ready_reachable cfg sel (Path.root : Path sel root root).reached T.rootStable h)
      T.bank rate)
  leafRoot : root.edges≤(S).cutoff→PageBank f ell key prec tw bw page→
    Meter (Block (T.frame (Path.root : Path sel root root).reached) ell)
  activeAfter : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel root c) (u : (Plan sel).Slot c),
    StoredSite T (p.ticket u) key prec tw bw page →
    ∀ h : (S).cutoff<((Plan sel).child c u).edges,
    Meter (ActiveMachine sel (ready_reachable cfg sel (Path.step p u).reached T.rootStable h) T.bank rate)
  leafAfter : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel root c) (u : (Plan sel).Slot c),
    StoredSite T (p.ticket u) key prec tw bw page →
    ((Plan sel).child c u).edges≤(S).cutoff → PageBank f ell key prec tw bw page →
    Meter (Block (T.frame (Path.step p u).reached) ell)

variable (A : OnlineOperators T key prec tw bw page rate)
variable (boot : ∀ w : (Plan sel).Slot root,
  Meter (StoredSite T ((Path.root : Path sel root root).ticket w) key prec tw bw page))
variable (req : ∀ {v : Ticket sel root} (X : StoredSite T v key prec tw bw page)
  (u : (Plan sel).Slot v.child),Meter (FixedRequest X u))

def fromActualInputMeters : OnlineMachine T key prec tw bw page rate where
  modeWidth := A.modeWidth
  initial := boot
  demand := fun X u=>meteredSelectedDemand (req X u)
  activeRoot := A.activeRoot
  leafRoot := A.leafRoot
  activeAfter := A.activeAfter
  leafAfter := A.leafAfter

theorem actual_input_meter_projection (w : (Plan sel).Slot root) :
    (fromActualInputMeters A boot req).initial w=boot w := rfl

theorem actual_full_machine_uses_increment_without_callback_law :
    UsesChildIncrement (fromActualInputMeters A boot req) := by
  intro c p w u
  exact selected_demand_uses_real_increment
    (req (sourceState (fromActualInputMeters A boot req) p w) u)

#print axioms fromActualInputMeters
#print axioms actual_input_meter_projection
#print axioms actual_full_machine_uses_increment_without_callback_law
end
end J6R55Public

