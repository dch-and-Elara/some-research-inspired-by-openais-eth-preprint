import J6R15ModeCostRun
import J6R15ModeCostSpace

/-! Combine the paid delay with actual mathematical outputs. The
proof transcript may collect results, but the machine interface emits
one tuple and need not buffer any previously emitted tuple. -/
namespace J6R15ModeCost
open AOracleMachineTime

def NextExact {q : ℕ} (n : ℕ) (xs : List (List ℕ)) : Pulse q→Prop
  | .again _ => False
  | .halt => xs=[]
  | .emit w t => ∃ ys,xs=w.map Word.val::ys ∧ t.wellFormed n ∧ Runs n t ys (.ascend [])

theorem untilEvent_semantics {q n : ℕ} (k : ℕ) (s : State q) (hs : s.wellFormed n)
    (hK : quietRank n s≤k) (xs : List (List ℕ)) (h : Runs n s xs (.ascend [])) :
    NextExact n xs (untilEvent n k s).result := by
  induction k generalizing s xs with
  | zero => have := quietRank_pos n s; omega
  | succ k ih =>
    cases h with
    | done => simp [untilEvent,step,NextExact]
    | quiet hstep hrun =>
      obtain ⟨hWF,hRank⟩ := step_silent _ _ hs hstep
      simpa only [untilEvent,hstep] using ih _ hWF (by omega) _ hrun
    | emit hstep hrun =>
      obtain ⟨hWF,_⟩ := step_emit _ _ _ hs hstep
      simp only [untilEvent,hstep,NextExact]
      exact ⟨_,rfl,hWF,hrun⟩

def delayCap (q n : ℕ) : ℕ := (2*n+1)*transitionCap q n

theorem one_paid_event {q n : ℕ} (s : State q) (hs : s.wellFormed n)
    (xs : List (List ℕ)) (h : Runs n s xs (.ascend [])) :
    let z := untilEvent n (2*n+1) s
    NextExact n xs z.result ∧ z.steps≤delayCap q n :=
  ⟨untilEvent_semantics _ s hs (quietRank_bound s hs) xs h,(paid_delay s hs).2⟩

/-- A proof transcript of successive events. Appending to the external
write-only output tape is included in the leaf meter of step; this
record is not a working-memory buffer of the streaming machine. -/
def collect {q : ℕ} (n : ℕ) : ℕ → State q → Meter (List (List (Word q)) × Bool)
  | 0,_ => ⟨([],false),0⟩
  | k+1,s =>
    let z := untilEvent n (2*n+1) s
    match z.result with
    | .again _ => ⟨([],false),z.steps⟩
    | .halt => ⟨([],true),z.steps⟩
    | .emit w t =>
      let r := collect n k t
      ⟨(w::r.result.1,r.result.2),z.steps+r.steps⟩

theorem collect_exact {q n : ℕ} (k : ℕ) (s : State q) (hs : s.wellFormed n)
    (xs : List (List ℕ)) (h : Runs n s xs (.ascend [])) (hk : xs.length+1≤k) :
    let r := collect n k s
    r.result.2=true ∧ r.result.1.map (List.map Word.val)=xs ∧
    r.steps≤(xs.length+1)*delayCap q n := by
  induction k generalizing s xs with
  | zero => omega
  | succ k ih =>
    obtain ⟨hnext,hc⟩ := one_paid_event s hs xs h
    cases H : (untilEvent n (2*n+1) s).result with
    | again t =>
      have N : NextExact n xs (.again t) := H ▸ hnext
      exact False.elim N
    | halt =>
      have N : NextExact n xs (.halt : Pulse q) := H ▸ hnext
      have E : xs=[] := N
      subst xs
      simp only [collect,H,List.length_nil,Nat.zero_add,List.map_nil,one_mul,true_and]
      exact hc
    | emit w t =>
      have N : NextExact n xs (.emit w t) := H ▸ hnext
      obtain ⟨ys,rfl,hW,hR⟩ := N
      have hK : ys.length+1≤k := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hk
      obtain ⟨hB,hY,hT⟩ := ih t hW ys hR hK
      simp only [collect,H,List.map_cons,List.length_cons,hB,hY,true_and]
      change (untilEvent n (2*n+1) s).steps+(collect n k t).steps≤(ys.length+1+1)*delayCap q n
      rw [Nat.succ_mul (ys.length+1) (delayCap q n)]
      exact (Nat.add_le_add hc hT).trans_eq (Nat.add_comm _ _)

theorem all_tuple_cost {q : ℕ} (hq : 0<q) (ws : List (Word q)) (p : Word q)
    (hp : ∀ w∈ws,0<w.val) (hP : 0<p.val) :
    let xs := strictTuples (ws.map Word.val) p.val
    ∃ s : State q,
      (start ws p).result=.again s ∧ s.wellFormed ws.length ∧
      let run := collect ws.length (xs.length+1) s
      run.result.2=true ∧ run.result.1.map (List.map Word.val)=xs ∧
      (start ws p).steps+run.steps ≤
        16*q+14+4*(ws.length+1)*(q+1)+(xs.length+1)*delayCap q ws.length := by
  obtain ⟨_,hRun⟩ := stream_all_exact hq ws p hp
  obtain ⟨R,hS,hRan⟩ := hRun (by omega)
  have hW : (State.enter ws R []).wellFormed ws.length := by
    simp [State.wellFormed,StackShape]
  obtain ⟨hB,hEq,hC⟩ := collect_exact _ _ hW _ hRan le_rfl
  refine ⟨_,hS,hW,hB,hEq,?_⟩
  exact Nat.add_le_add (start_exact hq ws p).2 hC

#print axioms untilEvent_semantics
#print axioms one_paid_event
#print axioms collect_exact
#print axioms all_tuple_cost
end J6R15ModeCost


