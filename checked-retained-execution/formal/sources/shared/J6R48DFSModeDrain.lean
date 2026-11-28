import J6R48DFSModeLoop
import J6R25PreparedSupplyDrain
import J6R25PreparedSupplyModeDecode

/-! The native fold can run to the real halt event, without storing
a count of remaining legal tuples. The ranking witness and expected
tuple list are proof-only, not a reserve menu passed to the runtime. -/
namespace J6R48DFS
open AOracleMachineTime J6R15ModeCost J6R25PreparedSupply

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {q n : ℕ} {A : Type*}

def modeDrain (op : A→List (Word q)→Meter A) (p : Pending q n) (a : A) (fee : ℕ) :
    Meter (A×Bool) :=
  let z := p.pulse
  match e : z.result with
  | .again _ => ⟨(a,false),fee+z.steps⟩
  | .halt => ⟨(a,true),fee+z.steps⟩
  | .emit w _ =>
    let out := op a w
    modeDrain op (p.tail e) out.result (fee+z.steps+out.steps)
termination_by p.ghostLen
decreasing_by exact p.tail_smaller e

theorem drain_matches_bounded (k : ℕ) (p : Pending q n)
    (xs : List (List ℕ)) (h : Runs n p.state xs (.ascend [])) (cap : xs.length+1≤k)
    (op : A→List (Word q)→Meter A) (a : A) (fee : ℕ) :
    modeDrain op p a fee=modeLoop n op k p.state a fee := by
  induction k generalizing p xs a fee with
  | zero => omega
  | succ k ih =>
    cases e : p.pulse.result with
    | again u => exact (p.no_again e).elim
    | halt =>
      have eh : (untilEvent n (2*n+1) p.state).result=.halt := e
      rw [modeDrain]
      simp only [modeLoop,eh]
      split
      · rename_i _ h1
        rw [e] at h1
        cases h1
      · rfl
      · rename_i _ _ h1
        rw [e] at h1
        cases h1
    | emit w u =>
      obtain ⟨ys,rfl,_,hY⟩ := p.next_data e h
      have capY : ys.length+1≤k := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using cap
      have eh : (untilEvent n (2*n+1) p.state).result=.emit w u := e
      rw [modeDrain]
      simp only [modeLoop,eh]
      split
      · rename_i _ h1
        rw [e] at h1
        cases h1
      · rename_i h1
        rw [e] at h1
        cases h1
      · rename_i w' u' h1
        have b := h1.symm.trans e
        cases b
        exact ih (p.tail h1) ys hY capY (op a w).result
          (fee+p.pulse.steps+(op a w).steps)

theorem halt_driven_fold_exact (p : Pending q n) (xs : List (List ℕ))
    (h : Runs n p.state xs (.ascend []))
    (op : A→List (Word q)→Meter A) (a : A) (fee : ℕ) :
    let out := modeDrain op p a fee
    let ref := foldExpected op xs a
    out.result=(ref.result,true) ∧ out.steps≤fee+ref.steps+(xs.length+1)*delayCap q n := by
  have eq := drain_matches_bounded (xs.length+1) p xs h le_rfl op a fee
  exact eq ▸ (modeLoop_exact n (xs.length+1) p.state p.valid xs h le_rfl op a fee)

theorem genuine_weighted_stream_fold (hq : 0<q) (ws : List (Word q)) (p : Word q)
    (hp : 0<p.val) (hW : ∀ w∈ws,0<w.val)
    (op : A→List (Word q)→Meter A) (a : A) :
    let X := strictTuples (ws.map Word.val) p.val
    ∃ P : Pending q ws.length,
      (start ws p).result=.again P.state ∧
      let out := modeDrain op P a (start ws p).steps
      out.result=((foldExpected op X a).result,true) ∧
      out.steps ≤ (16*q+14+4*(ws.length+1)*(q+1))+
        (foldExpected op X a).steps+(X.length+1)*delayCap q ws.length := by
  obtain ⟨_,hStart⟩ := stream_all_exact hq ws p hW
  obtain ⟨w,emit,run⟩ := hStart hp.ne'
  have hState : (State.enter ws w []).wellFormed ws.length := by simp [State.wellFormed,StackShape]
  let P : Pending q ws.length := ⟨.enter ws w [],hState,⟨_,run⟩⟩
  obtain ⟨v,price⟩ := halt_driven_fold_exact P _ run op a (start ws p).steps
  refine ⟨P,emit,v,price.trans ?_⟩
  exact Nat.add_le_add_right (Nat.add_le_add_right (start_exact hq ws p).2 _) _

#print axioms modeDrain
#print axioms drain_matches_bounded
#print axioms halt_driven_fold_exact
#print axioms genuine_weighted_stream_fold
end J6R48DFS
