import J6R53PeakAddonCore
import J6R52CacheWholeScopeFee
import J6R52CacheWholeRun

/-! The exterior evaluator's actual first callback installs the real
first child's sidecar. Its bit count is proportional to the root's
edge count even though subsequent mounted frames are proportional to
the child's smaller edge count. -/
namespace J6R53PeakAddon
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R16ModeCost J6R36ChildFramedRoute J6R41StructuredAllPaths J6R48RawRoute J6R50SourceProducer
open J6R51Peak J6R51Online J6R51ParentFrames J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 17500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def exteriorCachedRead (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ)
    (initial : L) (a : (S).cutoff<r.edges) :
    ActiveChild (sel:=sel) (d:=ready_reachable cfg sel (Path.root : Path sel r r).reached T.rootStable a) T.bank :=
  let here : Path sel r r := .root
  let d := ready_reachable cfg sel here.reached T.rootStable a
  fun t z β g=>
    let w := addressed (sel:=sel) d t z β g
    project (bootBankDemand (M.initial w) retire (runCachedAfter M retire r here w)
      (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) initial)

theorem actual_root_active_uses_the_exterior_child_reader
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (a : (S).cutoff<r.edges) :
    let A := M.activeRoot a
    let here : Path sel r r := .root
    let done := A.result.eval M.modeWidth (reachable_positive T here.reached) T.vPositive hf
      (exteriorCachedRead M retire initial a)
    runCachedRoot M retire initial=⟨(done.result,initial),A.steps+done.steps⟩ := by
  dsimp only
  rw [runCachedRoot,dif_neg (Nat.not_le.mpr a)]
  rfl

theorem actual_first_read_passes_and_pays_the_same_installed_addon_bank
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial) (a : (S).cutoff<r.edges)
    (t : Center S r) (z : Probe S r) (β : NativeMenu (N sel) r t) (g : Fin 64) :
    let p : Path sel r r := .root
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let start := M.initial w
    let X := sourceState M p w
    let j := X.birth.job
    let incoming := installResidentBank X
    let child := runCachedAfter M retire r p w X incoming.result (afterOne initial j)
    exteriorCachedRead M retire initial a t z β g=
      ⟨child.result.1,start.steps+(publishFee initial j.entry j.offset j.built+
        (incoming.steps+child.steps)+retire j+4)⟩ ∧
    incoming.result.rows.length=2*r.edges := by
  let p : Path sel r r := .root
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let w := addressed (sel:=sel) d t z β g
  let low := T.bank (registerPrecision S r t) (register_positive d t)
  let bad : Meter (Block low ell) := zeroM low.hp
  let go := runCachedAfter M retire r p w
  have ready : JobsReady initial [(M.initial w).result.birth.job] := legal p w
  refine ⟨?_,true_resident_bank_rows (installResidentBank (sourceState M p w)).result⟩
  change project (bootBankDemand (M.initial w) retire go bad initial)=_
  rw [cached_boot_bank_is_paid_if_entered (M.initial w) retire go bad initial ready]
  rfl

#print axioms actual_root_active_uses_the_exterior_child_reader
#print axioms actual_first_read_passes_and_pays_the_same_installed_addon_bank
end
end J6R53PeakAddon
