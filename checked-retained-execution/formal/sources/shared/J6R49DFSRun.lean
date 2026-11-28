import J6R49DFSActive
import J6R48DFSRun

/-! One recursively executed program. An active call receives a
finite variable tape, starts the next-event cursor at each probe,
evaluates each actual group child with the live scoped directory,
and releases it before the next occurrence. Leaf and active words
are the same physical registers as in the printed Plan. -/
namespace J6R49DFS
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS

set_option autoImplicit false
set_option maxRecDepth 2700
set_option maxHeartbeats 12000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

structure StreamingResident {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
    {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
    {r : Call (PhysicalHost f ell)} {hf : f.Monic} (T : Prepared cfg sel r hf) (key prec tw bw page q : ℕ) where
  modeWidth : 0<q
  births : J6R33StatefulArithmeticPage.Births T key prec tw bw page
  rootLive : PageBank f ell key prec tw bw page→Prop
  rootStable : StableBank rootLive
  leaf : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c),
    c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff→PageBank f ell key prec tw bw page→Meter (Block (T.frame p.reached) ell)
  leafMatches : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (h : c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (B : PageBank f ell key prec tw bw page),opened births rootLive p B→
      (T.frame p.reached).decode (leaf p h B).result=(T.frame p.reached).decode (T.run c p.reached).result
  active : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (h : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges),
    ActiveMachine sel (ready_reachable cfg sel p.reached T.rootStable h) T.bank q

noncomputable def nativeStream
    (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) :
    SM L (Block (T.frame p.reached) ell) :=
  if stop : c.edges≤(S).cutoff then
    fun B=>let w := R.leaf p stop B
           ⟨(w.result,B),w.steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel p.reached T.rootStable active
    let A := R.active p active
    fun B=>
      let out := A.eval R.modeWidth (reachable_positive T p.reached) T.vPositive hf (fun t z β g=>
        let w := addressed (sel:=sel) d t z β g
        project (withScope retire (R.births p w).job
          (nativeStream R retire ((Plan sel).child c w) (.step p w))
          (zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp) B))
      ⟨(out.result,B),out.steps⟩
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

theorem stream_restores_bank (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (B : L) :
    (nativeStream R retire c p B).result.2=B := by
  by_cases stop : c.edges≤(S).cutoff
  · rw [nativeStream,dif_pos stop]
  · rw [nativeStream,dif_neg stop]

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

/-- The R33 metered leaf machine is a direct special case; this
adapter does not identify a different raw edge order with R33's. -/
noncomputable def StreamingResident.fromResident
    (R : PagedResident T key prec tw bw page) (hq : 0<q)
    (M : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (h : (S).cutoff<c.edges),
      ActiveMachine sel (ready_reachable cfg sel p.reached T.rootStable h) T.bank q) :
    StreamingResident T key prec tw bw page q where
  modeWidth := hq
  births := R.births
  rootLive := R.rootLive
  rootStable := R.stableRoot
  leaf p stop B := (R.leaf p stop).execute hf (T.frame p.reached) T.vPositive B
  leafMatches p stop B live :=
    (live_paged_leaf_source R p stop B live).trans (T.correctAt _ p.reached).symm
  active := M

set_option maxHeartbeats 17500000 in
theorem stream_matches_printed (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ)
    (initial : L) (origin : R.rootLive initial) (valid : ReadyOnStack R.births initial)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) :
    (T.frame p.reached).decode
      (nativeStream R retire c p (stackBank R.births initial p)).result.1=
      (sourceBlueprint sel r hf).program.run c := by
  by_cases stop : c.edges≤(S).cutoff
  · rw [nativeStream,dif_pos stop]
    let B := stackBank R.births initial p
    exact (R.leafMatches p stop B
      (stack_is_opened R.births initial R.rootLive R.rootStable origin valid p)).trans
      (T.correctAt c p.reached)
  · let a := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let A := R.active p a
    let B := stackBank R.births initial p
    let hp := reachable_positive T p.reached
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (withScope retire (R.births p w).job
        (nativeStream R retire ((Plan sel).child c w) (.step p w))
        (zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp) B)
    have child (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
        (T.bank (registerPrecision S c t) (register_positive d t)).decode (read t z β g).result=
        (sourceBlueprint sel r hf).program.run ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩) := by
      let w := addressed (sel:=sel) d t z β g
      let j := (R.births p w).job
      let F := T.bank (registerPrecision S c t) (register_positive d t)
      let qrun := nativeStream R retire ((Plan sel).child c w) (.step p w)
      let fallback : Meter (Block F ell) := zeroM F.hp
      have same := paid_scope_exact retire j qrun fallback B (valid p w)
      change F.decode (project (withScope retire j qrun fallback B)).result=_
      rw [same]
      exact stream_matches_printed R retire initial origin valid ((Plan sel).child c w) (.step p w)
    obtain ⟨x,_,xval,hvalue⟩ := actual_active_decoded cfg sel r hf p.reached d T.rootStable
      A.prior hp T.vPositive read child
    rw [nativeStream,dif_neg stop]
    change (T.bank c.prec hp).decode (A.eval R.modeWidth hp T.vPositive hf read).result=_
    rw [active_stream_value A R.modeWidth hp T.vPositive hf read,xval]
    exact hvalue
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

theorem whole_stream_scoped_source (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ)
    (initial : L) (origin : R.rootLive initial) (valid : ReadyOnStack R.births initial) :
    let run := nativeStream R retire r .root initial
    (T.frame (NativeReach.reflexive r)).decode run.result.1=(sourceBlueprint sel r hf).program.run r ∧
      run.result.2=initial :=
  ⟨stream_matches_printed R retire initial origin valid r .root,
    stream_restores_bank R retire r .root initial⟩

#print axioms nativeStream
#print axioms stream_restores_bank
#print axioms StreamingResident.fromResident
#print axioms stream_matches_printed
#print axioms whole_stream_scoped_source
end J6R49DFS
