import J6R52CacheSourceDemand
import J6R51OnlineVisit

/-! All addressed child continuations of one actual active parent get
the same mounted frame object. Each addresses the same printed slot
and invokes the same inherited runner after a real scope publication. -/
namespace J6R52CacheSource
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
open J6R51ParentFrames J6R51Online
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 10000000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def cachedAfterRead
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<((@Plan f ell s sel).child c u).edges)
    (B : L) (cache : CachedParentFrames X.site) :
    ActiveChild (sel:=sel)
      (d:=ready_reachable cfg sel (Path.step p u).reached T.rootStable a) T.bank := by
  let current := (@Plan f ell s sel).child c u
  let path := Path.step p u
  let d := ready_reachable cfg sel path.reached T.rootStable a
  exact fun t z β g =>
    let w := addressed (sel:=sel) d t z β g
    project (openCachedDemand (M.demand X w) cache retire
      (fun next=>runAfter M retire current path w next)
      (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) B)

theorem cached_after_read_exact
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<((@Plan f ell s sel).child c u).edges)
    (B : L) (cache : CachedParentFrames X.site) :
    cachedAfterRead M retire p u X a B cache=readAfter M retire p u X a B := by
  funext t z β g
  simp only [cachedAfterRead,readAfter,open_cached_demand_exact]

def cachedActiveAfter
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<((@Plan f ell s sel).child c u).edges)
    (B : L) (cache : CachedParentFrames X.site) :
    Meter (Block (T.frame (Path.step p u).reached) ell) :=
  let A := M.activeAfter p u X a
  let out := A.result.eval M.modeWidth (reachable_positive T (Path.step p u).reached) T.vPositive hf
    (cachedAfterRead M retire p u X a B cache)
  ⟨out.result,A.steps+out.steps⟩

theorem cached_active_after_is_actual
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<((@Plan f ell s sel).child c u).edges)
    (B : L) (cache : CachedParentFrames X.site) :
    cachedActiveAfter M retire p u X a B cache=project (runAfter M retire c p u X B) := by
  unfold cachedActiveAfter
  dsimp only
  rw [cached_after_read_exact,run_after_active_eq M retire p u X a B]
  rfl

#print axioms cached_after_read_exact
#print axioms cached_active_after_is_actual
end
end J6R52CacheSource
