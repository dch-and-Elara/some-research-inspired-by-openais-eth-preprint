import J6R25PreparedSupplyDrain
import J6R17ModeTapeRun

/-! The concrete tape is initialized once, drained until its native halt
bit, and parsed by the paid R17 sparse serializer. Mathematical tuple
count is only used to state the receipt and upper bound, not as fuel. -/
namespace J6R25PreparedSupply
open AOracleMachineTime J6R15ModeCost J6R17ModeTape

structure Batch (q : ℕ) where
  vectors : List (List (Word q))
  halted : Bool
  support : List (Option (List (RawMode q×Word q)))

theorem initial_pending {q : ℕ}
    (T : RawTape q) (hq : 0<q) (hp : 0<T.precision.val)
    (positive : ∀ x∈T.weights,0<x.val) {s : State q}
    (h : (start T.weights T.precision).result=.again s) :
    s.wellFormed T.weights.length ∧
      Runs T.weights.length s (strictTuples (T.weights.map Word.val) T.precision.val) (.ascend []) := by
  obtain ⟨u,hu,hRun⟩ := (stream_all_exact hq _ _ positive).2 hp.ne'
  rw [h] at hu
  have e := Pulse.again.inj hu
  subst s
  exact ⟨by simp [State.wellFormed,StackShape],hRun⟩

def emitBatch {q : ℕ} (a : ℕ) (T : RawTape q) (hq : 0<q)
    (hp : 0<T.precision.val) (positive : ∀ x∈T.weights,0<x.val) : Meter (Batch q) :=
  let b := start T.weights T.precision
  match e : b.result with
  | .halt => ⟨⟨[],false,[]⟩,b.steps+4⟩
  | .emit _ _ => ⟨⟨[],false,[]⟩,b.steps+4⟩
  | .again s =>
    let h := initial_pending T hq hp positive e
    let d := drain (⟨s,h.1,⟨_,h.2⟩⟩ : Pending q T.weights.length)
    let out := dispatchStream a T d.result.1
    ⟨⟨d.result.1,d.result.2,out.result⟩,b.steps+d.steps+out.steps+4⟩

def emitBatchCap (a q w m K : ℕ) : ℕ :=
  (16*q+14+4*(w+1)*(q+1))+(K+1)*delayCap q w+(m*dispatchStride a q+10)*K+4

theorem emit_batch_exact {q : ℕ} (a : ℕ) (T : RawTape q) (hq : 0<q)
    (hp : 0<T.precision.val) (positive : ∀ x∈T.weights,0<x.val)
    (hLen : T.weights.length=T.modes.length) :
    let out := emitBatch a T hq hp positive
    let xs := strictTuples (T.weights.map Word.val) T.precision.val
    out.result.halted=true ∧ out.result.vectors.map (List.map Word.val)=xs ∧
      out.result.support=out.result.vectors.map (fun v=>some (supportSpec T.modes v)) ∧
      out.steps≤emitBatchCap a q T.weights.length T.modes.length xs.length := by
  let xs := strictTuples (T.weights.map Word.val) T.precision.val
  obtain ⟨u,hu,hRun⟩ := (stream_all_exact hq _ _ positive).2 hp.ne'
  let c : Pending q T.weights.length := 
    ⟨.enter T.weights u [],by simp [State.wellFormed,StackShape],⟨_,hRun⟩⟩
  have h0 : drain c=collect T.weights.length (xs.length+1) c.state :=
    drain_transcript (xs.length+1) c hRun le_rfl
  have hd : (drain c).result.2=true ∧ (drain c).result.1.map (List.map Word.val)=xs ∧
      (drain c).steps≤(xs.length+1)*delayCap q T.weights.length := by
    rw [h0]
    exact collect_exact _ _ c.valid _ hRun le_rfl
  have hOK (v : List (Word q)) (hv : v∈(drain c).result.1) :
      v.length=T.modes.length := by
    have hPos (x : ℕ) (hx : x∈T.weights.map Word.val) : 0<x := by
      obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hx
      exact positive w hm
    have hall : (v.map Word.val)∈xs := by rw [←hd.2.1]; exact List.mem_map_of_mem hv
    have hL := ((strictTuples_exact _ _ hPos).2 _ |>.mp hall).1
    simpa only [List.length_map,hLen] using hL
  have dd := dispatchStream_exact a T (drain c).result.1 hOK
  have hN : (drain c).result.1.length=xs.length := by
    have e := congrArg List.length hd.2.1
    simpa only [List.length_map] using e
  rw [hN] at dd
  unfold emitBatch
  dsimp only
  split
  · rename_i h
    rw [hu] at h
    cases h
  · rename_i v t h
    rw [hu] at h
    cases h
  · rename_i t h
    have eq : t=c.state := Pulse.again.inj (h.symm.trans hu)
    subst t
    change (drain c).result.2=true ∧ (drain c).result.1.map (List.map Word.val)=xs ∧
      (dispatchStream a T (drain c).result.1).result=((drain c).result.1.map (fun v=>some (supportSpec T.modes v))) ∧
      (start T.weights T.precision).steps+(drain c).steps+(dispatchStream a T (drain c).result.1).steps+4≤
        emitBatchCap a q T.weights.length T.modes.length xs.length
    refine ⟨hd.1,hd.2.1,dd.1,?_⟩
    have hS := (start_exact hq T.weights T.precision).2
    have hD := hd.2.2
    have hF := dd.2
    unfold emitBatchCap
    omega

#print axioms initial_pending
#print axioms emit_batch_exact
end J6R25PreparedSupply

