import J6R51OnlineVisitLocal

/-! On the actual root and actual reached descendants, the new
transactional run computes the printed source value. The proof-side
stack is derived from the demand producer, not passed to the runner. -/
namespace J6R51Online
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3300
set_option maxHeartbeats 18000000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "P" => (Plan sel)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw page q)
variable (initial : PageBank f ell key prec tw bw page)

structure LeafAgreement : Prop where
  root : ∀ stop : r.edges≤(S).cutoff,
    (T.frame (Path.root : Path sel r r).reached).decode (M.leafRoot stop initial).result=
      (sourceBlueprint sel r hf).program.run r
  after : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (P).Slot c)
    (stop : ((P).child c u).edges≤(S).cutoff),
    let A := (T.frame (Path.step p u).reached)
    let x := sourceState M p u
    let B := stackBank (borns M) initial (.step p u)
    A.decode (M.leafAfter p u x stop B).result=
      (sourceBlueprint sel r hf).program.run ((P).child c u)

theorem run_after_decodes_source
    (M : OnlineMachine T key prec tw bw page q) (initial : PageBank f ell key prec tw bw page)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (valid : ReadyOnStack (borns M) initial) (leaves : LeafAgreement M initial)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (P).Slot c) :
    let B := stackBank (borns M) initial (.step p u)
    let X := sourceState M p u
    (T.frame (Path.step p u).reached).decode (runAfter M retire c p u X B).result.1=
      (sourceBlueprint sel r hf).program.run ((P).child c u) := by
  let current := (P).child c u
  let path := Path.step p u
  let X := sourceState M p u
  let B := stackBank (borns M) initial path
  change (T.frame path.reached).decode (runAfter M retire c p u X B).result.1=
    (sourceBlueprint sel r hf).program.run current
  by_cases stop : current.edges≤(S).cutoff
  · rw [runAfter,dif_pos stop]
    exact leaves.after p u stop
  · let a := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel path.reached T.rootStable a
    let A := M.activeAfter p u X a
    let hp := reachable_positive T path.reached
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openDemand (M.demand X w) retire (fun nx=>runAfter M retire current path w nx)
        (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) B)
    have child (t : Center S current) (z : Probe S current)
        (β : NativeMenu (N sel) current t) (g : Fin 64) :
        (T.bank (registerPrecision S current t) (register_positive d t)).decode (read t z β g).result=
        (sourceBlueprint sel r hf).program.run ((P).child current ⟨⟨t,z,β,g⟩,d.active⟩) := by
      let w := addressed (sel:=sel) d t z β g
      have ok : JobsReady B [(M.demand X w).result.advance.next.birth.job] := valid path w
      let K := M.demand X w
      let F := T.bank (registerPrecision S current t) (register_positive d t)
      let fallback : Meter (Block F ell) := zeroM F.hp
      let descend := fun nx=>runAfter M retire current path w nx
      have H := open_demand_from_ready K retire descend fallback B ok
      change F.decode (project (openDemand K retire descend fallback B)).result=_
      rw [H]
      exact run_after_decodes_source M initial retire valid leaves current path w
    obtain ⟨x,_,xval,hvalue⟩ := actual_active_decoded cfg sel r hf path.reached d T.rootStable
      A.result.prior hp T.vPositive read child
    rw [runAfter,dif_neg stop]
    change (T.bank current.prec hp).decode (A.result.eval M.modeWidth hp T.vPositive hf read).result=_
    rw [active_stream_value A.result M.modeWidth hp T.vPositive hf read,xval]
    exact hvalue
termination_by ((Plan sel).child c u).edges
decreasing_by exact (Plan sel).smaller _ _

theorem root_run_decodes_source
    (M : OnlineMachine T key prec tw bw page q) (initial : PageBank f ell key prec tw bw page)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (valid : ReadyOnStack (borns M) initial) (leaves : LeafAgreement M initial) :
    (T.frame (Path.root : Path sel r r).reached).decode (runRoot M retire initial).result.1=
      (sourceBlueprint sel r hf).program.run r := by
  by_cases stop : r.edges≤(S).cutoff
  · rw [runRoot,dif_pos stop]
    exact leaves.root stop
  · let a := Nat.lt_of_not_ge stop
    let path : Path sel r r := .root
    let d := ready_reachable cfg sel path.reached T.rootStable a
    let A := M.activeRoot a
    let hp := reachable_positive T path.reached
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (bootDemand (M.initial w) retire (runAfter M retire r path w)
        (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) initial)
    have child (t : Center S r) (z : Probe S r)
        (β : NativeMenu (N sel) r t) (g : Fin 64) :
        (T.bank (registerPrecision S r t) (register_positive d t)).decode (read t z β g).result=
        (sourceBlueprint sel r hf).program.run ((P).child r ⟨⟨t,z,β,g⟩,d.active⟩) := by
      let w := addressed (sel:=sel) d t z β g
      let H := M.initial w
      let F := T.bank (registerPrecision S r t) (register_positive d t)
      let bad : Meter (Block F ell) := zeroM F.hp
      have ok : JobsReady initial [H.result.birth.job] := valid path w
      have h := boot_demand_exact H retire (runAfter M retire r path w) bad initial ok
      change F.decode (project (bootDemand H retire (runAfter M retire r path w) bad initial)).result=_
      rw [h]
      exact run_after_decodes_source M initial retire valid leaves r path w
    obtain ⟨x,_,xval,hvalue⟩ := actual_active_decoded cfg sel r hf path.reached d T.rootStable
      A.result.prior hp T.vPositive read child
    rw [runRoot,dif_neg stop]
    change (T.bank r.prec hp).decode (A.result.eval M.modeWidth hp T.vPositive hf read).result=_
    rw [active_stream_value A.result M.modeWidth hp T.vPositive hf read,xval]
    exact hvalue

theorem full_online_selected_source
    (M : OnlineMachine T key prec tw bw page q) (initial : PageBank f ell key prec tw bw page)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (valid : ReadyOnStack (borns M) initial) (leaves : LeafAgreement M initial) :
    let out := runRoot M retire initial
    (T.frame (Path.root : Path sel r r).reached).decode out.result.1=
        (sourceBlueprint sel r hf).program.run r ∧ out.result.2=initial :=
  ⟨root_run_decodes_source M initial retire valid leaves,root_run_restores_bank M retire initial⟩

#print axioms run_after_decodes_source
#print axioms root_run_decodes_source
#print axioms full_online_selected_source
end
end J6R51Online