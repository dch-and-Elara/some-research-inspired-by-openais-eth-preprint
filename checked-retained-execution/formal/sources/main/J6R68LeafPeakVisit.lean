import J6R68RecursivePeakVisit
import J6R51OnlineFeeDefs

/-! An exact stopped R66 invocation is the real leaf on the
published live bank and the same stored site. The concrete
positive owner adapter must still be attached separately. -/
namespace J6R68.LeafPeak
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48RawRoute J6R52CacheWhole
open J6ActiveSchedule J6R9Recursive J6R16ModeCost J6R21Ancestor J6R48DFS
open J6R10Repack J6R34ChildPath J6R54PeakInput J6R53PeakAddon J6R55CachedLedger J6R52Peak
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R26DescriptorTree J6R24MeteredRecursion J6R49DFS
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R68.RecursivePeak
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4400
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 9200000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

theorem actual_stopped_r66_visit_is_the_entered_leaf_meter
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) (w : (P).Slot c)
    (stop : ((P).child c w).edges≤(S).cutoff) :
    let current := Path.step p w
    let leaf := readLeaf M initial current stop
    liveVisit M F E retire initial own current=
      ⟨(leaf.result,stackBank (borns M) initial current),leaf.steps⟩ := by
  let X := sourceState M p w
  let bank := stackBank (borns M) initial (.step p w)
  change J6R66Active.runAfter M F retire c p w X (installResidentBank X).result bank rfl=
    ⟨((M.leafAfter p w X stop bank).result,bank),(M.leafAfter p w X stop bank).steps⟩
  exact stopped_after_uses_original_leaf M F retire p w X (installResidentBank X).result bank rfl stop

#print axioms actual_stopped_r66_visit_is_the_entered_leaf_meter
end
end J6R68.LeafPeak