import J6R52CacheWholeRun

/-! Pointwise raw comparison at any actual reached descendant, with
no requirement that registry publication succeeds. Both runners see
the same outgoing descriptor and the same live directory when it
does succeed, and use the same fallback otherwise. -/
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
set_option maxRecDepth 3500
set_option maxHeartbeats 20500000
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

theorem cached_after_pointwise
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X) (B : L) :
    (runCachedAfter M retire c p u X resident B).result=(runAfter M retire c p u X B).result := by
  let current := (@Plan f ell s sel).child c u
  let path := Path.step p u
  by_cases stop : current.edges≤(SP).cutoff
  · rw [runCachedAfter,dif_pos stop,runAfter,dif_pos stop]
  · let active := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel path.reached T.rootStable active
    let A := M.activeAfter p u X active
    let mounted := mountResident X resident
    let hp := reachable_positive T path.reached
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openBankDemand (M.demand X w) mounted.result retire
        (fun next live=>runCachedAfter M retire current path w next live)
        (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) B)
    let old := readAfter M retire p u X active B
    have same (t : Center SP current) (z : Probe SP current)
        (β : NativeMenu (N sel) current t) (g : Fin 64) :
        (read t z β g).result=(old t z β g).result := by
      let w := addressed (sel:=sel) d t z β g
      let K := M.demand X w
      let F := T.bank (registerPrecision SP current t) (register_positive d t)
      let bad : Meter (Block F ell) := zeroM F.hp
      let go := fun next live=>runCachedAfter M retire current path w next live
      let prev := fun next=>runAfter M retire current path w next
      change (openBankDemand K mounted.result retire go bad B).result.1=
        (openDemand K retire prev bad B).result.1
      refine congrArg Prod.fst (open_bank_demand_value K mounted.result retire go prev bad B ?_)
      intro next live bank
      exact congrArg Prod.fst (cached_after_pointwise M retire current path w next live bank)
    have eq := streaming_value_congr A.result M.modeWidth hp T.vPositive hf read old same
    rw [runCachedAfter,dif_neg stop,run_after_active_eq M retire p u X active B]
    exact congrArg (fun value : Block (T.frame path.reached) ell=>(value,B)) eq
termination_by ((@Plan f ell s sel).child c u).edges
decreasing_by exact (@Plan f ell s sel).smaller _ _

#print axioms cached_after_pointwise
end
end J6R52CacheWhole
