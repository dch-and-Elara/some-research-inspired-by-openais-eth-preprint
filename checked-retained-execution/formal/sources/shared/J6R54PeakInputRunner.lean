import J6R54PeakInputShare
import J6R52CacheWholeRun

/-! The single-explicit-emission helper can be used at every deep
call of one cache-aware runner without changing either value or the
existing Meter. This replaces no outer boot loader, and makes no
statement about allocations by a code generator or by user callbacks. -/
namespace J6R54PeakInput
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
open J6R51ParentFrames J6R51Online J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 29500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def runCachedAfterSingleEmission
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ)
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
          project (openBankDemandSingleEmission acquire mounted.result retire
            (fun next live=>runCachedAfterSingleEmission M retire current path w next live)
            (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) B))
      ⟨(out.result,B),mounted.steps+A.steps+out.steps⟩
termination_by ((@Plan f ell s sel).child c u).edges
decreasing_by exact (@Plan f ell s sel).smaller ((@Plan f ell s sel).child c u) w

theorem all_depth_single_emission_preserves_cached_result_and_cost
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X) :
    runCachedAfterSingleEmission M retire c p u X resident=runCachedAfter M retire c p u X resident := by
  let current := (@Plan f ell s sel).child c u
  let path := Path.step p u
  funext B
  by_cases stop : current.edges≤(SP).cutoff
  · rw [runCachedAfterSingleEmission,dif_pos stop,runCachedAfter,dif_pos stop]
  · let active := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel path.reached T.rootStable active
    let A := M.activeAfter p u X active
    let mounted := mountResident X resident
    let hp := reachable_positive T path.reached
    let revised : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openBankDemandSingleEmission (M.demand X w) mounted.result retire
        (fun next live=>runCachedAfterSingleEmission M retire current path w next live)
        (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) B)
    let prior : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openBankDemand (M.demand X w) mounted.result retire
        (fun next live=>runCachedAfter M retire current path w next live)
        (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) B)
    have same : revised=prior := by
      funext t z β g
      let w := addressed (sel:=sel) d t z β g
      let acq := M.demand X w
      let F := T.bank (registerPrecision SP current t) (register_positive d t)
      let bad : Meter (Block F ell) := zeroM F.hp
      let nextOne := fun next live=>runCachedAfterSingleEmission M retire current path w next live
      let nextOld := fun next live=>runCachedAfter M retire current path w next live
      have eq : nextOne=nextOld := by
        funext next live
        exact all_depth_single_emission_preserves_cached_result_and_cost M retire current path w next live
      change project (openBankDemandSingleEmission acq mounted.result retire nextOne bad B)=
        project (openBankDemand acq mounted.result retire nextOld bad B)
      rw [single_local_emission_is_exactly_the_original_scoped_meter,eq]
    rw [runCachedAfterSingleEmission,dif_neg stop,runCachedAfter,dif_neg stop]
    let A0 := A.result.eval M.modeWidth hp T.vPositive hf
    change (⟨((A0 revised).result,B),mounted.steps+A.steps+(A0 revised).steps⟩ : Meter _) =
      ⟨((A0 prior).result,B),mounted.steps+A.steps+(A0 prior).steps⟩
    rw [same]
termination_by ((@Plan f ell s sel).child c u).edges
decreasing_by exact (@Plan f ell s sel).smaller _ _

#print axioms runCachedAfterSingleEmission
#print axioms all_depth_single_emission_preserves_cached_result_and_cost
end
end J6R54PeakInput
