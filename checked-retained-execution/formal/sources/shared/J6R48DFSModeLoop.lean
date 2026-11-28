import J6R15ModeCostPaid
import J6R17ModeTapeTuple

/-! Sequential consumption of actual weighted-mode events. In contrast
with the proof-only collect transcript, the measured loop passes one
tuple, one continuation cursor and one accumulator to the next stage.
The number of completed tuples is not a size parameter of a live list.
The callback's work and scratch remain its own explicitly open model. -/
namespace J6R48DFS
open AOracleMachineTime J6R15ModeCost

set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {q : ℕ} {A : Type*}

/-- Tail-position mode consumption, including the running fee counter.
Fuel is a semantic watchdog; this theorem does not include a bit
implementation of the fuel or meter counters. -/
def modeLoop (n : ℕ) (op : A→List (Word q)→Meter A) :
    ℕ→State q→A→ℕ→Meter (A×Bool)
  | 0,_,a,fee => ⟨(a,false),fee⟩
  | k+1,s,a,fee =>
    let event := untilEvent n (2*n+1) s
    match event.result with
    | .again _ => ⟨(a,false),fee+event.steps⟩
    | .halt => ⟨(a,true),fee+event.steps⟩
    | .emit w t =>
      let u := op a w
      modeLoop n op k t u.result (fee+event.steps+u.steps)

def foldExpected (op : A→List (Word q)→Meter A) : List (List ℕ)→A→Meter A
  | [],a => ⟨a,0⟩
  | w::ws,a =>
    let z := op a (w.map word)
    let k := foldExpected op ws z.result
    ⟨k.result,z.steps+k.steps⟩

theorem canonical_tuple_words (w : List (Word q)) :
    (w.map Word.val).map word=w := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,valued_word,ih]

theorem modeLoop_exact (n k : ℕ) (s : State q) (hs : s.wellFormed n)
    (xs : List (List ℕ)) (h : Runs n s xs (.ascend [])) (hk : xs.length+1≤k)
    (op : A→List (Word q)→Meter A) (a : A) (fee : ℕ) :
    let u := modeLoop n op k s a fee
    let v := foldExpected op xs a
    u.result=(v.result,true) ∧ u.steps≤fee+v.steps+(xs.length+1)*delayCap q n := by
  induction k generalizing s xs a fee with
  | zero => omega
  | succ k ih =>
    obtain ⟨hnext,hcost⟩ := one_paid_event s hs xs h
    cases e : (untilEvent n (2*n+1) s).result with
    | again t =>
      have N : NextExact n xs (.again t) := e ▸ hnext
      exact False.elim N
    | halt =>
      have N : NextExact n xs (.halt : Pulse q) := e ▸ hnext
      have H : xs=[] := N
      subst xs
      simp only [modeLoop,e,foldExpected,List.length_nil,Nat.zero_add,one_mul,Nat.add_zero,true_and]
      exact Nat.add_le_add_left hcost _
    | emit w t =>
      have N : NextExact n xs (.emit w t) := e ▸ hnext
      obtain ⟨ys,rfl,hT,hN⟩ := N
      have kk : ys.length+1≤k := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hk
      let v := op a w
      let e' := untilEvent n (2*n+1) s
      obtain ⟨value,cost⟩ := ih t hT ys hN kk v.result (fee+e'.steps+v.steps)
      simp only [modeLoop,e,foldExpected,canonical_tuple_words]
      change (modeLoop n op k t v.result (fee+e'.steps+v.steps)).result=
        ((foldExpected op ys v.result).result,true) ∧ _
      refine ⟨value,cost.trans ?_⟩
      change fee+e'.steps+v.steps+(foldExpected op ys v.result).steps+(ys.length+1)*delayCap q n≤
        fee+(v.steps+(foldExpected op ys v.result).steps)+(ys.length+1+1)*delayCap q n
      rw [Nat.add_mul (ys.length+1) 1 (delayCap q n),Nat.one_mul]
      change e'.steps ≤ delayCap q n at hcost
      omega

/-- A conservative logical bit-field allocation across one next-event
boundary, counting the pending tuple and current/successor cursors
rather than only the final state. No interpolation or callback word
storage is in this counter. -/
def modeBoundaryWords (s : State q) (out : Pulse q) : ℕ :=
  stateWords s +
  match out with
  | .again t => stateWords t
  | .halt => 0
  | .emit w t => w.length+stateWords t

theorem event_cursor_live_bound {n : ℕ} (s : State q) (h : s.wellFormed n) :
    modeBoundaryWords s (untilEvent n (2*n+1) s).result≤2*(n+2)^2+n := by
  have h0 := stateWords_bound s h
  cases e : (untilEvent n (2*n+1) s).result with
  | again t =>
    have r : Ready n (.again t) := e ▸ (paid_delay s h).1
    cases r
  | halt =>
    simp only [modeBoundaryWords,Nat.add_zero]
    omega
  | emit w t =>
    have pres : Ready n (.emit w t) := e ▸ (paid_delay s h).1
    cases pres with
    | emitted _ _ hw ht =>
      have h1 := stateWords_bound t ht
      simp only [modeBoundaryWords,hw]
      omega

theorem paid_start_stream_exact (hq : 0<q) (ws : List (Word q)) (p : Word q) (hp : 0<p.val)
    (hW : ∀ w∈ws,0<w.val) (k : ℕ)
    (hK : (strictTuples (ws.map Word.val) p.val).length+1≤k)
    (op : A→List (Word q)→Meter A) (a : A) :
    ∃ s, (start ws p).result=.again s ∧ s.wellFormed ws.length ∧
      let X := strictTuples (ws.map Word.val) p.val
      let run := modeLoop ws.length op k s a (start ws p).steps
      run.result=((foldExpected op X a).result,true) ∧
      run.steps ≤
        (16*q+14+4*(ws.length+1)*(q+1))+(foldExpected op X a).steps+(X.length+1)*delayCap q ws.length := by
  obtain ⟨_,h⟩ := stream_all_exact hq ws p hW
  obtain ⟨v,path,run⟩ := h hp.ne'
  have hw : (State.enter ws v []).wellFormed ws.length := by simp [State.wellFormed,StackShape]
  obtain ⟨val,price⟩ := modeLoop_exact _ _ _ hw _ run hK op a (start ws p).steps
  refine ⟨_,path,hw,val,price.trans ?_⟩
  exact Nat.add_le_add_right (Nat.add_le_add_right (start_exact hq ws p).2 _) _

#print axioms canonical_tuple_words
#print axioms modeLoop_exact
#print axioms event_cursor_live_bound
#print axioms paid_start_stream_exact
end J6R48DFS
