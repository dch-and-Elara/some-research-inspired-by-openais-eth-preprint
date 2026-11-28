import J6R63OrdinalActive
import J6R63OrdinalCoordinate
import J6R63OrdinalDispatch
import J6R54PeakInputRootRunner

/-! The new descendant request ABI carries one real raw emission.
Only its proof-level freshness and compatibility refer to the archive.
Boot, leaf and active source producers retain the established ABI;
there is no old full-mode dispatch or supplied LocalLoad field. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
open J6R51ParentFrames J6R51Online J6R52CacheWhole J6R54PeakInput
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4900
set_option maxHeartbeats 7200000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "PlanAt" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Here" => (Path.root : Path sel r r)

structure Base (T : Prepared cfg sel r hf) (key prec tw bw page q : ℕ) where
  modeWidth : 0<q
  initial : (u : (PlanAt).Slot r)→Meter (StoredSite T ((Here).ticket u) key prec tw bw page)
  activeRoot : ∀ h : (SP).cutoff<r.edges,
    Meter (ActiveMachine sel (ready_reachable cfg sel (Here).reached T.rootStable h) T.bank q)
  leafRoot : r.edges≤(SP).cutoff → PageBank f ell key prec tw bw page → Meter (Block (T.frame (Here).reached) ell)
  activeAfter : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (PlanAt).Slot c),
    StoredSite T (p.ticket u) key prec tw bw page →
    ∀ h : (SP).cutoff<((PlanAt).child c u).edges,
    Meter (ActiveMachine sel (ready_reachable cfg sel (Path.step p u).reached T.rootStable h) T.bank q)
  leafAfter : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (PlanAt).Slot c),
    StoredSite T (p.ticket u) key prec tw bw page →
    ((PlanAt).child c u).edges≤(SP).cutoff → PageBank f ell key prec tw bw page → Meter (Block (T.frame (Path.step p u).reached) ell)

def Base.ofOnline (M : OnlineMachine T key prec tw bw page q) : Base T key prec tw bw page q :=
  ⟨M.modeWidth,M.initial,M.activeRoot,M.leafRoot,@M.activeAfter,@M.leafAfter⟩


structure Program (B : Base T key prec tw bw page (q+1)) (b : ℕ) where
  ordinalWidth : 0<b
  archive : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (PlanAt).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (on : (SP).cutoff<((PlanAt).child c u).edges) (t : Center SP ((PlanAt).child c u)),
    HonestArchive ((B.activeAfter p u X on).result.tape t).tape.result
      (centreArchiveOrdinal T (Path.step p u) on t) b
  prepare : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (PlanAt).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (_cache : CachedParentFrames X.site)
    (on : (SP).cutoff<((PlanAt).child c u).edges) (t : Center SP ((PlanAt).child c u))
    (z : Probe SP ((PlanAt).child c u)) (β : NativeMenu (N sel) ((PlanAt).child c u) t) (g : Fin 64)
    (_raw : List (Word (q+1))),
    let d := ready_reachable cfg sel (Path.step p u).reached T.rootStable on
    let w := addressed (sel:=sel) d t z β g
    Meter (Request (X:=X) (w:=w) (q:=q) ((B.activeAfter p u X on).result.tape t).tape.result)


#print axioms Base
#print axioms Base.ofOnline
#print axioms Program
end
end J6R63Ordinal
