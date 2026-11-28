import J6R52PeakCachedStack
import J6R52CacheWholeScopeFee

/-! The actual recursive active phase passes the selected cache itself
to the next real checked demand, not an independently defined sibling
cache or a merely value-equivalent reader. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R49DFS J6R50SourceProducer J6R51Online J6R51Peak J6R51ParentFrames
open J6R48RawRoute J6R36ChildFramedRoute J6R52CacheWhole J6R52CacheSource

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 19000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def sourceCachedRead (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ)
    (initial : L) (p : Path sel r c) (u : (P).Slot c) (a : (S).cutoff<((P).child c u).edges) :
    ActiveChild (sel:=sel) (d:=ready_reachable cfg sel (Path.step p u).reached T.rootStable a) T.bank :=
  let X := sourceState M p u
  let here := Path.step p u
  let d := ready_reachable cfg sel here.reached T.rootStable a
  fun t z β g=>
    let w := addressed (sel:=sel) d t z β g
    project (openBankDemand (M.demand X w) (sourceMounted (M:=M) p u).result retire
      (fun next bank=>runCachedAfter M retire ((P).child c u) here w next bank)
      (zeroM (T.bank (registerPrecision S ((P).child c u) t) (register_positive d t)).hp)
      (stackBank (borns M) initial here))

theorem cached_active_phase_uses_the_selected_frame_cache
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (p : Path sel r c) (u : (P).Slot c) (a : (S).cutoff<((P).child c u).edges) :
    let X := sourceState M p u
    let here := Path.step p u
    let B := stackBank (borns M) initial here
    let active := M.activeAfter p u X a
    let evaluated := active.result.eval M.modeWidth (reachable_positive T here.reached) T.vPositive hf
      (sourceCachedRead M retire initial p u a)
    runCachedAfter M retire c p u X (installResidentBank X).result B=
      ⟨(evaluated.result,B),(sourceMounted (M:=M) p u).steps+active.steps+evaluated.steps⟩ := by
  dsimp only
  rw [runCachedAfter,dif_neg (Nat.not_le.mpr a)]
  rfl

theorem exact_cached_source_read_has_the_next_native_cache_bank
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial)
    (p : Path sel r c) (u : (P).Slot c) (a : (S).cutoff<((P).child c u).edges)
    (t : Center S ((P).child c u)) (z : Probe S ((P).child c u))
    (β : NativeMenu (N sel) ((P).child c u) t) (g : Fin 64) :
    let X := sourceState M p u
    let here := Path.step p u
    let d := ready_reachable cfg sel here.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let B := stackBank (borns M) initial here
    let K := M.demand X w
    let next := K.result.advance.next
    let job := next.birth.job
    let got := runCachedAfter M retire ((P).child c u) here w next
      (installResidentBank next).result (afterOne B job)
    sourceCachedRead M retire initial p u a t z β g=
      ⟨got.result.1,paidAcquisition K+(publishFee B job.entry job.offset job.built+got.steps+retire job+4)⟩ := by
  let X := sourceState M p u
  let here := Path.step p u
  let d := ready_reachable cfg sel here.reached T.rootStable a
  let w := addressed (sel:=sel) d t z β g
  let B := stackBank (borns M) initial here
  let K := M.demand X w
  let go := fun next bank=>runCachedAfter M retire ((P).child c u) here w next bank
  let bad : Meter (Block (T.bank (registerPrecision S ((P).child c u) t) (register_positive d t)) ell) :=
    zeroM (T.bank (registerPrecision S ((P).child c u) t) (register_positive d t)).hp
  let collect (next : StoredSite T (here.ticket w) key prec tw bw page) :
      Meter (Block (T.frame (Path.step here w).reached) ell×L) :=
    let job := next.birth.job
    let out := go next (installResidentBank next).result (afterOne B job)
    ⟨(out.result.1,B),paidAcquisition K+(publishFee B job.entry job.offset job.built+out.steps+retire job+4)⟩
  have paid := cached_child_enters_same_paid_scope K (sourceMounted (M:=M) p u).result retire
    go bad B (legal here w)
  have wrote : openBankDemand K (sourceMounted (M:=M) p u).result retire go bad B =
      collect (cachedAdvance X w K.result (sourceMounted (M:=M) p u).result).next := paid.2
  change project (openBankDemand K (sourceMounted (M:=M) p u).result retire go bad B)=
    project (collect K.result.advance.next)
  exact congrArg project (wrote.trans (congrArg collect paid.1))

#print axioms cached_active_phase_uses_the_selected_frame_cache
#print axioms exact_cached_source_read_has_the_next_native_cache_bank
end
end J6R52Peak
