import J6R58OrdinalSpacePulse
import Mathlib.Data.List.NodupEquivFin

/-! A ghost alignment relating the literal cursor suffix to the
legacy support's arbitrarily chosen order. Only if this alignment
holds does the live ordinal equal the archival index. The list is
used in a Prop in the theorem, not in numberedPulse or successor. -/
namespace J6R58OrdinalSpace
open AOracleMachineTime J6R15ModeCost J6R25PreparedSupply
set_option autoImplicit false
set_option maxHeartbeats 15000000

def RankAlignment {X : Type*} {q n bits : ℕ}
    (encode : X→List ℕ) (order : List X) (p : Pending q n) (i : Word bits) : Prop :=
  ∃ seen remain,order=seen++remain ∧ i.val=seen.length ∧
    Runs n p.state (remain.map encode) (.ascend [])

theorem real_first_pending_starts_at_zero_rank {X : Type*} {q n bits : ℕ}
    (encode : X→List ℕ) (order : List X) (p : Pending q n)
    (tr : Runs n p.state (order.map encode) (.ascend [])) :
    RankAlignment encode order p (firstOrdinal bits).result :=
  ⟨[],order,rfl,(first_ordinal_is_paid_zero bits).1,tr⟩

theorem index_of_unseen_head_at_prefix {X : Type*} [BEq X] [LawfulBEq X]
    (seen tail : List X) (x : X) (fresh : x∉seen) :
    (seen++x::tail).idxOf x=seen.length := by
  rw [List.idxOf_append,if_neg fresh,List.idxOf_cons_self,Nat.zero_add]

theorem actual_next_pulse_preserves_an_aligned_archival_rank {X : Type*} [BEq X] [LawfulBEq X]
    {q n bits : ℕ} (encode : X→List ℕ) (order : List X) (unique : order.Nodup)
    (p : Pending q n) (i : Word bits) (pos : 0<bits) (room : order.length<2^bits)
    (aligned : RankAlignment encode order p i) {raw : List (Word q)} {state : State q}
    (emitted : p.pulse.result=.emit raw state) :
    ∃ x,raw.map Word.val=encode x ∧ i.val=order.idxOf x ∧
      RankAlignment encode order (p.tail emitted) (increment i).result := by
  obtain ⟨seen,remain,whole,old,tracks⟩ := aligned
  obtain ⟨rest,em,valid,tracksNext⟩ := p.next_data emitted tracks
  cases remain with
  | nil => simp at em
  | cons x tail =>
    change encode x::tail.map encode=raw.map Word.val::rest at em
    have emitEq := List.cons.inj em
    have exactOrder : order=seen++x::tail := whole
    have allUnique : (x::(seen++tail)).Nodup :=
      List.nodup_middle.mp (exactOrder ▸ unique)
    have absent : x∉seen := fun inSeen=>
      (List.nodup_cons.mp allUnique).1 (List.mem_append.mpr (Or.inl inSeen))
    have index := index_of_unseen_head_at_prefix seen tail x absent
    have fit : i.val+1<2^bits := by
      rw [old]
      rw [exactOrder,List.length_append,List.length_cons] at room
      omega
    have next := (increment_exact pos i fit).1
    have kept : order=(seen++[x])++tail :=
      exactOrder.trans (List.append_assoc seen [x] tail).symm
    have newRank : (increment i).result.val=(seen++[x]).length := by
      rw [next,old,List.length_append]
      rfl
    have more : Runs n (p.tail emitted).state (tail.map encode) (.ascend []) := by
      rw [emitEq.2]
      exact tracksNext
    exact ⟨x,emitEq.1.symm,old.trans (by rw [exactOrder,index]),⟨seen++[x],tail,kept,newRank,more⟩⟩

#print axioms real_first_pending_starts_at_zero_rank
#print axioms index_of_unseen_head_at_prefix
#print axioms actual_next_pulse_preserves_an_aligned_archival_rank
end J6R58OrdinalSpace
