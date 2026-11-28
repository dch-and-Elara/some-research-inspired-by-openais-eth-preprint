
import J6R30ProducedGateRegistryJobs
import J6R30ProducedGateRegistryPrefix

/-! Depth-first publication of an already resident occurrence forest.
Each node uses the same paired physical publisher; children see the
parent's installed capsule, and the trailing siblings see all earlier
installations. This closes the directory-state induction, not the
generation of a forest from an arbitrary compact root. -/
namespace J6R30ProducedGateRegistry
open AOracleMachineTime J6R21Ancestor

inductive Forest (J : Type*) where
  | empty
  | node (entry : J) (children siblings : Forest J)

def Forest.inOrder {J : Type*} : Forest J→List J
  | .empty => []
  | .node j c s => j::c.inOrder++s.inOrder

def Forest.walkFee {J : Type*} : Forest J→ℕ
  | .empty => 2
  | .node _ c s => c.walkFee+s.walkFee+6

variable {key prec tw bw : ℕ} {D : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D

def publishDFS (B : L) : Forest J→Meter (L×Bool)
  | .empty => ⟨(B,true),2⟩
  | .node j children siblings =>
    let born := j.install B
    if born.result.2 then
      let descend := publishDFS born.result.1 children
      if descend.result.2 then
        let resume := publishDFS descend.result.1 siblings
        ⟨resume.result,born.steps+descend.steps+resume.steps+6⟩
      else ⟨descend.result,born.steps+descend.steps+4⟩
    else ⟨born.result,born.steps+4⟩

set_option maxHeartbeats 2700000 in
theorem dfs_publication_receipt (B : L) (F : Forest J) (h : JobsReady B F.inOrder) :
    publishDFS B F =
      ⟨(afterJobs B F.inOrder,true),chronologicalBill B F.inOrder+F.walkFee⟩ := by
  induction F generalizing B with
  | empty => rfl
  | node j c s ihc ihs =>
    change JobsReady B (j::(c.inOrder++s.inOrder)) at h
    obtain ⟨root,following⟩ := next_job_exact B j (c.inOrder++s.inOrder) h
    obtain ⟨hc,hs⟩ := jobs_split_ready (afterOne B j) c.inOrder s.inOrder following
    have cRun := ihc (afterOne B j) hc
    have sRun := ihs (afterJobs (afterOne B j) c.inOrder) hs
    rw [publishDFS,root]
    dsimp only
    rw [cRun]
    dsimp only
    rw [sRun]
    dsimp only
    simp only [Forest.inOrder,Forest.walkFee,afterJobs,after_jobs_concatenate,chronologicalBill,
      chronological_split,if_true]
    congr 1
    omega

theorem dfs_old_capsule_receipt (B : L) (F : Forest J) (h : JobsReady B F.inOrder)
    (addr : J6R15ModeCost.Word key) (old : ∀ j∈F.inOrder,j.identifier≠addr) :
    let out := publishDFS B F
    locate addr out.result.1.records=
      ⟨(locate addr B.records).result,F.inOrder.length*refHeadFee key+(locate addr B.records).steps⟩ := by
  have hNew : ∀ r∈(F.inOrder.map Job.immutable).reverse,r.address≠addr := by
    intro row mem
    rw [List.mem_reverse] at mem
    obtain ⟨j,atJob,rfl⟩ := List.mem_map.mp mem
    exact old j atJob
  rw [dfs_publication_receipt B F h]
  dsimp only
  rw [(after_jobs_views B F.inOrder).2]
  simpa only [List.length_reverse,List.length_map] using
    reference_front_fee addr (F.inOrder.map Job.immutable).reverse B.records hNew

#print axioms dfs_publication_receipt
#print axioms dfs_old_capsule_receipt
end J6R30ProducedGateRegistry



