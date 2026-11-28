import J6R52CacheWholePrep

/-! Unlike the single-parent R52 adapter, every actual selected
recursive continuation here calls this same cache-aware runner with
the real newly installed child's resident bank. -/
namespace J6R52CacheWhole
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
set_option maxRecDepth 3400
set_option maxHeartbeats 15000000
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

def runCachedAfter
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X) :
    SM L (Block (T.frame (Path.step p u).reached) ell) :=
  let current := (@Plan f ell s sel).child c u
  let path := Path.step p u
  if stop : current.edges≤(SP).cutoff then
    fun B=>
      let w := M.leafAfter p u X stop B
      ⟨(w.result,B),w.steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel path.reached T.rootStable active
    let A := M.activeAfter p u X active
    fun B=>
      let mounted := mountResident X resident
      let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf
        (fun t z β g=>
          let w := addressed (sel:=sel) d t z β g
          let acquire := M.demand X w
          project (openBankDemand acquire mounted.result retire
            (fun next live=>runCachedAfter M retire current path w next live)
            (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) B))
      ⟨(out.result,B),mounted.steps+A.steps+out.steps⟩
termination_by ((@Plan f ell s sel).child c u).edges
decreasing_by exact (@Plan f ell s sel).smaller ((@Plan f ell s sel).child c u) w

theorem cached_after_restores_bank
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X) (B : L) :
    (runCachedAfter M retire c p u X resident B).result.2=B := by
  by_cases stop : ((@Plan f ell s sel).child c u).edges≤(SP).cutoff
  · rw [runCachedAfter,dif_pos stop]
  · rw [runCachedAfter,dif_neg stop]

def runCachedRoot
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) :
    SM L (Block (T.frame (Path.root : Path sel r r).reached) ell) :=
  if stop : r.edges≤(SP).cutoff then
    fun B=>
      let w := M.leafRoot stop B
      ⟨(w.result,B),w.steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let path : Path sel r r := .root
    let d := ready_reachable cfg sel path.reached T.rootStable active
    let A := M.activeRoot active
    fun B=>
      let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf
        (fun t z β g=>
          let w := addressed (sel:=sel) d t z β g
          project (bootBankDemand (M.initial w) retire (runCachedAfter M retire r path w)
            (zeroM (T.bank (registerPrecision SP r t) (register_positive d t)).hp) B))
      ⟨(out.result,B),A.steps+out.steps⟩

theorem cached_root_restores_bank
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (B : L) :
    (runCachedRoot M retire B).result.2=B := by
  by_cases stop : r.edges≤(SP).cutoff
  · rw [runCachedRoot,dif_pos stop]
  · rw [runCachedRoot,dif_neg stop]

#print axioms runCachedAfter
#print axioms cached_after_restores_bank
#print axioms runCachedRoot
#print axioms cached_root_restores_bank
end
end J6R52CacheWhole
