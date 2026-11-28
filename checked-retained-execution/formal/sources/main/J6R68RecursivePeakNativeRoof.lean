import J6R68RecursivePeakCurrent
import J6R52PeakModePath

/-! The bounded selected raw tape is the current centre output only.
It is not multiplied by the number of recursive invocations or
centres, nor does this count include the raw builder's work heap. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R52Peak J6R50Peak J6R14LayoutCost
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active J6R49DFS
open J6ActiveSchedule J6R10Repack
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4450
set_option maxHeartbeats 14500000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def nativeCentreRoof (s C cw q pAbs : ℕ) : ℕ :=
  let R := (6*(C*s))*pAbs
  cw+q+R*(6*Nat.clog 2 s+6*Nat.clog 2 s+q+q+q)+R*q+q

theorem actual_raw_centre_outputs_have_uniform_selected_roof
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (a : (S).cutoff<c.edges) (t : Center S c) :
    liveCentreOutputBits M F E B own p a t≤nativeCentreRoof s C cw q
      (absolutePrecision s r.edges r.prec) := by
  let d := readyAtPath T p a
  let tape := ((liveActiveAt M F E B own p a).result.tape t).tape.result
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have hE : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact d.edgeCount
  have lo := absolute_register_precision_cap cfg sel T.rootStable p a t
  have m := actual_edges_uniform T p
  have shape := physical_roster_length (packing sel d) (centerIndex d t)
    tape.modes tape.nodup tape.allModes
  rw [hE] at shape
  have n : tape.modes.length≤(6*(C*s))*absolutePrecision s r.edges r.prec :=
    shape.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ m) lo)
  have axis : (S).levelBits c.depth≤Nat.clog 2 s := by
    simpa only [printedParams,printedShape] using bits_le_lam (Nat.clog 2 s) c.depth
  have keys : 6*(S).levelBits c.depth+6*(S).levelBits c.depth+q+q+q≤
      6*Nat.clog 2 s+6*Nat.clog 2 s+q+q+q :=
    Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Nat.mul_le_mul_left 6 axis) (Nat.mul_le_mul_left 6 axis)) q) q) q
  have bytes := real_live_centre_has_exact_selected_outputs M F E B own p a t
  rw [bytes]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul n keys) _) (Nat.mul_le_mul_right q n)) _

#print axioms actual_raw_centre_outputs_have_uniform_selected_roof
end
end J6R68.RecursivePeak