
import J6R30ProducedGateRegistryLedger

/-! Mathematical snapshots and receipts for a list of genuine publication
jobs. The executor uses only the raw header and actual compiler.
The tag/result witnesses are used solely to describe the expected
immutable directory state and never supply the reader's answer. -/
namespace J6R30ProducedGateRegistry
open AOracleMachineTime J6R21Ancestor

structure Job {key prec tw bw : ℕ} (D : Type*) where
  entry : Meter (DirRow key)
  offset : ℕ
  ctx : CentreContext tw bw
  built : Meter (Option D)
  birth : J6R15ModeCost.Word prec
  expected : D
  validTag : loadAt prec offset entry.result.bytes=⟨some birth,headerReadFee prec offset⟩
  validBody : built.result=some expected

variable {key prec tw bw : ℕ} {D : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D

def Job.identifier (j : J) := j.entry.result.id

def Job.immutable (j : J) : RefRow key (Stored key prec tw bw D) :=
  publishedRow j.entry.result j.birth j.ctx j.expected

def Job.install (j : J) (B : L) : Meter (L×Bool) :=
  publishCompiled B j.entry j.offset j.ctx j.built

def afterOne (B : L) (j : J) : L := ⟨j.entry.result::B.headers,j.immutable::B.records⟩

def afterJobs (B : L) : List J→L
  | [] => B
  | j::js => afterJobs (afterOne B j) js

def chronologicalBill (B : L) : List J→ℕ
  | [] => 0
  | j::js => publishFee B j.entry j.offset j.built+chronologicalBill (afterOne B j) js

theorem after_jobs_concatenate (B : L) (u v : List J) :
    afterJobs B (u++v)=afterJobs (afterJobs B u) v := by
  induction u generalizing B with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,afterJobs]
    exact ih (afterOne B x)

theorem chronological_split (B : L) (u v : List J) :
    chronologicalBill B (u++v)=chronologicalBill B u+chronologicalBill (afterJobs B u) v := by
  induction u generalizing B with
  | nil => simp [chronologicalBill,afterJobs]
  | cons x xs ih =>
    simp only [List.cons_append,chronologicalBill,afterJobs,ih,Nat.add_assoc]

theorem after_jobs_views (B : L) (js : List J) :
    (afterJobs B js).headers=(js.map (fun j=>j.entry.result)).reverse++B.headers ∧
    (afterJobs B js).records=(js.map Job.immutable).reverse++B.records := by
  induction js generalizing B with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨h,r⟩ := ih (afterOne B x)
    simp only [afterJobs]
    rw [h,r]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,afterOne,and_self]

theorem after_jobs_synced (B : L) (s : B.synced) (js : List J) : (afterJobs B js).synced := by
  induction js generalizing B with
  | nil => exact s
  | cons x xs ih =>
    have ok : (afterOne B x).synced :=
      (same_published_record x.entry.result x.birth x.ctx x.expected B s).1
    exact ih (afterOne B x) ok

def JobsReady (B : L) (js : List J) : Prop :=
  B.synced ∧ (js.map Job.identifier).Nodup ∧
    ∀ j∈js,∀ r∈B.headers,r.id≠j.identifier

theorem next_job_exact (B : L) (j : J) (js : List J) (h : JobsReady B (j::js)) :
    j.install B=⟨(afterOne B j,true),publishFee B j.entry j.offset j.built⟩ ∧
    JobsReady (afterOne B j) js := by
  have ready := h.2.2 j List.mem_cons_self
  refine ⟨publish_compiled_exact B h.1 j.entry j.offset j.ctx j.built j.expected j.validBody
    j.birth j.validTag ready,?_⟩
  have hn := List.nodup_cons.mp h.2.1
  refine ⟨(after_jobs_synced B h.1 [j]),hn.2,?_⟩
  intro x hx row atRow
  change row∈j.entry.result::B.headers at atRow
  rcases List.mem_cons.mp atRow with rfl|old
  · intro eq
    change j.identifier=x.identifier at eq
    exact hn.1 (eq.symm ▸ List.mem_map_of_mem hx)
  · exact h.2.2 x (List.mem_cons_of_mem _ hx) row old

theorem jobs_split_ready (B : L) (u v : List J) (h : JobsReady B (u++v)) :
    JobsReady B u ∧ JobsReady (afterJobs B u) v := by
  have disjoint := h.2.1
  rw [List.map_append,List.nodup_append] at disjoint
  refine ⟨⟨h.1,disjoint.1,fun j hj=>h.2.2 j (List.mem_append_left _ hj)⟩,
    after_jobs_synced B h.1 u,disjoint.2.1,?_⟩
  intro j hj row mem
  rw [(after_jobs_views B u).1,List.mem_append] at mem
  rcases mem with added|initial
  · rw [List.mem_reverse] at added
    obtain ⟨k,hk,eq⟩ := List.mem_map.mp added
    intro equals
    have a : k.identifier∈u.map Job.identifier := List.mem_map_of_mem hk
    have b : j.identifier∈v.map Job.identifier := List.mem_map_of_mem hj
    have c : k.identifier=j.identifier := (congrArg DirRow.id eq).trans equals
    exact disjoint.2.2 _ a _ b c
  · exact h.2.2 j (List.mem_append_right _ hj) row initial

#print axioms after_jobs_views
#print axioms after_jobs_synced
#print axioms chronological_split
#print axioms next_job_exact
#print axioms jobs_split_ready
end J6R30ProducedGateRegistry


