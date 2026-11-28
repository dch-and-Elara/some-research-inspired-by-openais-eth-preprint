import J6R48DFSPath
import J6R33StatefulArithmeticPageRun

/-! A scope uses the real paired publisher and persistent list tails.
A successful descent sees the new header and the new per-page atlas.
On return the caller's original view is restored. Numerical output
alone leaves the scope; retained descriptors refer only to live keys.
Restoring this view is not a re-interpretation of the append-only bill. -/
namespace J6R48DFS
open scoped Polynomial
open J1PPrinted J6R11Blueprint
open AOracleMachineTime J6ActiveRun J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage

set_option autoImplicit false
set_option linter.unusedSectionVars false

section Wrapper
variable {key prec tw bw : ℕ} {D A : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D

/-- The tariff is explicit; no claim that deallocating the payload or
acquiring its words is free. The mutable object is the visible tail
pointer to the pair of persistent directory lists. -/
def withScope (retire : J→ℕ) (j : J) (go : SM L A) (bad : Meter A) : SM L A :=
  fun B =>
    let q := j.install B
    if q.result.2 then
      let out := go q.result.1
      ⟨(out.result.1,B),q.steps+out.steps+retire j+4⟩
    else ⟨(bad.result,B),q.steps+bad.steps+4⟩

theorem scope_always_restores (retire : J→ℕ) (j : J) (go : SM L A) (bad : Meter A) (B : L) :
    (withScope retire j go bad B).result.2=B := by
  unfold withScope
  dsimp only
  split <;> rfl

theorem paid_scope_exact (retire : J→ℕ) (j : J) (go : SM L A) (bad : Meter A)
    (B : L) (legal : JobsReady B [j]) :
    withScope retire j go bad B=
      ⟨((go (afterOne B j)).result.1,B),
        publishFee B j.entry j.offset j.built+(go (afterOne B j)).steps+retire j+4⟩ := by
  rw [withScope,(next_job_exact B j [] legal).1]
  simp only [if_true]

theorem scope_id_can_recur (retire : J→ℕ) (j : J) (go : SM L A) (bad : Meter A)
    (B : L) :
    withScope retire j go bad (withScope retire j go bad B).result.2=
      withScope retire j go bad B ∧
    ¬ JobsReady (afterOne B j) [j] := by
  refine ⟨congrArg (withScope retire j go bad) (scope_always_restores retire j go bad B),?_⟩
  intro h
  have forbidden := h.2.2 j List.mem_cons_self j.entry.result
    (show j.entry.result ∈ (afterOne B j).headers from List.mem_cons_self)
  exact forbidden rfl
end Wrapper

section Native
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

/-- The youngest published occurrence is first, matching a directory scan. -/
def stackJobs (born : Births T key prec tw bw page) : {par : Call (PhysicalHost f ell)} → Path sel r par→List J
  | _, .root => []
  | _, .step p w => (born p w).job :: stackJobs born p

/-- Mathematical view used to state the invariant; the interpreter
does not reconstruct this list before every entry. -/
def stackBank (born : Births T key prec tw bw page) (initial : L) : {par : Call (PhysicalHost f ell)} → Path sel r par→L
  | _, .root => initial
  | _, .step p w => afterOne (stackBank born initial p) (born p w).job

theorem stack_bank_views (born : Births T key prec tw bw page) (initial : L) (p : Path sel r c) :
    (stackBank born initial p).headers=(stackJobs born p).map (fun j=>j.entry.result)++initial.headers ∧
    (stackBank born initial p).records=(stackJobs born p).map Job.immutable++initial.records := by
  induction p with
  | root => exact ⟨rfl,rfl⟩
  | step p w ih =>
    simp only [stackBank,afterOne,stackJobs,List.map_cons,List.cons_append,ih.1,ih.2,and_self]

theorem stack_jobs_length (born : Births T key prec tw bw page) (p : Path sel r c) :
    (stackJobs born p).length=moves p := by
  induction p with
  | root => rfl
  | step p w ih => simp only [stackJobs,List.length_cons,moves,ih]

theorem stack_directory_size (born : Births T key prec tw bw page) (initial : L) (p : Path sel r c) :
    (stackBank born initial p).headers.length=initial.headers.length+moves p ∧
    (stackBank born initial p).records.length=initial.records.length+moves p := by
  obtain ⟨a,b⟩ := stack_bank_views born initial p
  simp only [a,b,List.length_append,List.length_map,stack_jobs_length,Nat.add_comm,and_self]

/-- Keys need only be fresh against the immutable root and the active
ancestor chain. The R33 global injectivity condition is not imposed
on distinct siblings which cannot both be visible. -/
def ReadyOnStack (born : Births T key prec tw bw page) (initial : L) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
    JobsReady (stackBank born initial p) [(born p w).job]

theorem stack_is_opened (born : Births T key prec tw bw page) (initial : L)
    (rootLive : L→Prop) (stable : StableBank rootLive)
    (root : rootLive initial) (valid : ReadyOnStack born initial) (p : Path sel r c) :
    opened born rootLive p (stackBank born initial p) := by
  induction p with
  | root => exact root
  | step p w ih => exact enter_opened born stable p w _ [] (valid p w) ih

theorem scoped_birth_live (born : Births T key prec tw bw page) (initial : L)
    (rootLive : L→Prop) (stable : StableBank rootLive)
    (root : rootLive initial) (valid : ReadyOnStack born initial) (p : Path sel r c)
    (j : J) (on : OnPath born j p) :
    J6R32StatefulArithmetic.IsLive j (stackBank born initial p) :=
  ancestor_paged_live born j p on _ (stack_is_opened born initial rootLive stable root valid p)

theorem visible_occurrence_limit (born : Births T key prec tw bw page) (initial : L)
    (p : Path sel r c) (d₀ : r.depth=0) :
    (stackBank born initial p).records.length ≤ initial.records.length+J6R16ModeCost.pathLimit s C := by
  have a := stack_directory_size born initial p
  have b := printed_stack_level_bound cfg T.rootStable d₀ p
  have e := (stack_exact_depth p).2
  omega
end Native

#print axioms scope_always_restores
#print axioms paid_scope_exact
#print axioms scope_id_can_recur
#print axioms stack_bank_views
#print axioms stack_jobs_length
#print axioms stack_directory_size
#print axioms stack_is_opened
#print axioms scoped_birth_live
#print axioms visible_occurrence_limit
end J6R48DFS
