import J6R52CacheWholeAfter
import J6R51OnlineCorrect

/-! End-to-end equality to the same selected R51 source runner,
pointwise even on its defined fallback. Exact source decoding uses
the same explicit ready-on-stack and terminal guards as R51. -/
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
set_option maxHeartbeats 18000000
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

theorem cached_root_pointwise (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (B : L) :
    (runCachedRoot M retire B).result=(runRoot M retire B).result := by
  by_cases stop : r.edges≤(SP).cutoff
  · rw [runCachedRoot,dif_pos stop,runRoot,dif_pos stop]
  · let active := Nat.lt_of_not_ge stop
    let path : Path sel r r := .root
    let d := ready_reachable cfg sel path.reached T.rootStable active
    let A := M.activeRoot active
    let hp := reachable_positive T path.reached
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (bootBankDemand (M.initial w) retire (runCachedAfter M retire r path w)
        (zeroM (T.bank (registerPrecision SP r t) (register_positive d t)).hp) B)
    let old := readRoot M retire active B
    have same (t : Center SP r) (z : Probe SP r)
        (β : NativeMenu (N sel) r t) (g : Fin 64) :
        (read t z β g).result=(old t z β g).result := by
      let w := addressed (sel:=sel) d t z β g
      let K := M.initial w
      let F := T.bank (registerPrecision SP r t) (register_positive d t)
      let bad : Meter (Block F ell) := zeroM F.hp
      let go := runCachedAfter M retire r path w
      let prev := runAfter M retire r path w
      change (bootBankDemand K retire go bad B).result.1=(bootDemand K retire prev bad B).result.1
      refine congrArg Prod.fst (boot_bank_value K retire go prev bad B ?_)
      intro next live bank
      exact congrArg Prod.fst (cached_after_pointwise M retire r path w next live bank)
    have eq := streaming_value_congr A.result M.modeWidth hp T.vPositive hf read old same
    rw [runCachedRoot,dif_neg stop,run_root_active_eq M retire active B]
    exact congrArg (fun value : Block (T.frame path.reached) ell=>(value,B)) eq

theorem fully_cached_selected_source
    [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (M : OnlineMachine T key prec tw bw page q) (B : L)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (valid : ReadyOnStack (borns M) B) (leaves : LeafAgreement M B) :
    let out := runCachedRoot M retire B
    (T.frame (Path.root : Path sel r r).reached).decode out.result.1=
      (sourceBlueprint sel r hf).program.run r ∧ out.result.2=B := by
  dsimp only
  rw [cached_root_pointwise]
  exact full_online_selected_source M B retire valid leaves

#print axioms cached_root_pointwise
#print axioms fully_cached_selected_source
end
end J6R52CacheWhole
