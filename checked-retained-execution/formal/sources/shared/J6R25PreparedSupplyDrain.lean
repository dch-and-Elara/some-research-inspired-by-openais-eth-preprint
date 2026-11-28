import J6R15ModeCostPaid

/-! A halt-driven native mode drain. The pending trace and ranking
function are erased proof data: the evaluator never precomputes the
total number of tuples or looks at the mathematical future list.
Only the actual transition probe and actual halt/emit bit are used. -/
namespace J6R25PreparedSupply
open J6R15ModeCost AOracleMachineTime

structure Pending (q n : ℕ) where
  state : State q
  valid : state.wellFormed n
  trace : ∃ xs,Runs n state xs (.ascend [])

def Pending.pulse {q n : ℕ} (c : Pending q n) :=
  untilEvent n (2*n+1) c.state

theorem Pending.no_again {q n : ℕ} (c : Pending q n) {u : State q}
    (h : c.pulse.result=.again u) : False := by
  obtain ⟨xs,tr⟩ := c.trace
  have e := (one_paid_event c.state c.valid xs tr).1
  change NextExact n xs c.pulse.result at e
  rw [h] at e
  exact e

theorem Pending.next_data {q n : ℕ} (c : Pending q n) {w : List (Word q)} {u : State q}
    (h : c.pulse.result=.emit w u) {xs : List (List ℕ)} (tr : Runs n c.state xs (.ascend [])) :
    ∃ ys,xs=w.map Word.val::ys ∧ u.wellFormed n ∧ Runs n u ys (.ascend []) := by
  have e := (one_paid_event c.state c.valid xs tr).1
  change NextExact n xs c.pulse.result at e
  rw [h] at e
  exact e

theorem Pending.emit_valid {q n : ℕ} (c : Pending q n) {w : List (Word q)} {u : State q}
    (h : c.pulse.result=.emit w u) : u.wellFormed n ∧ ∃ ys,Runs n u ys (.ascend []) := by
  obtain ⟨xs,tr⟩ := c.trace
  obtain ⟨ys,_,hu,hr⟩ := c.next_data h tr
  exact ⟨hu,ys,hr⟩

def Pending.tail {q n : ℕ} (c : Pending q n) {w : List (Word q)} {u : State q}
    (h : c.pulse.result=.emit w u) : Pending q n :=
  ⟨u,(c.emit_valid h).1,(c.emit_valid h).2⟩

theorem Pending.has_rank {q n : ℕ} (c : Pending q n) :
    ∃ v : ℕ,∃ xs,Runs n c.state xs (.ascend []) ∧ xs.length=v := by
  obtain ⟨xs,h⟩ := c.trace
  exact ⟨xs.length,xs,h,rfl⟩

noncomputable def Pending.ghostLen {q n : ℕ} (c : Pending q n) : ℕ := by
  classical
  exact Nat.find c.has_rank

theorem Pending.tail_smaller {q n : ℕ} (c : Pending q n) {w : List (Word q)} {u : State q}
    (h : c.pulse.result=.emit w u) : (c.tail h).ghostLen<c.ghostLen := by
  classical
  obtain ⟨xs,ht,hN⟩ := Nat.find_spec c.has_rank
  obtain ⟨ys,rfl,_,hu⟩ := c.next_data h ht
  have hy : (c.tail h).ghostLen≤ys.length := Nat.find_min' (c.tail h).has_rank ⟨ys,hu,rfl⟩
  change ys.length+1=c.ghostLen at hN
  omega

def drain {q n : ℕ} (c : Pending q n) : Meter (List (List (Word q)) × Bool) :=
  let z := c.pulse
  match e : z.result with
  | .again _ => ⟨([],false),z.steps⟩
  | .halt => ⟨([],true),z.steps⟩
  | .emit w t =>
      let r := drain (c.tail e)
      ⟨(w::r.result.1,r.result.2),z.steps+r.steps⟩
termination_by c.ghostLen
decreasing_by exact c.tail_smaller e

theorem drain_transcript {q n : ℕ} (k : ℕ) (c : Pending q n)
    {xs : List (List ℕ)} (tr : Runs n c.state xs (.ascend [])) (cap : xs.length+1≤k) :
    drain c=collect n k c.state := by
  induction k generalizing c xs with
  | zero => omega
  | succ k ih =>

    cases h : c.pulse.result with
    | again s => exact (c.no_again h).elim
    | halt =>
      have hr : (untilEvent n (2*n+1) c.state).result=.halt := h
      rw [drain]
      simp only [collect,hr]
      split
      · rename_i _ hp
        rw [h] at hp
        cases hp
      · rfl
      · rename_i _ _ hp
        rw [h] at hp
        cases hp
    | emit w s =>
      obtain ⟨ys,rfl,_,hRan⟩ := c.next_data h tr
      have hCap : ys.length+1≤k := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using cap
      have hTail := ih (c.tail h) hRan hCap
      have hr : (untilEvent n (2*n+1) c.state).result=.emit w s := h
      rw [drain]
      simp only [collect,hr]
      split
      · rename_i _ hp
        rw [h] at hp
        cases hp
      · rename_i hp
        rw [h] at hp
        cases hp
      · rename_i v u hp
        have eq := hp.symm.trans h
        cases eq
        rw [hTail]
        rfl

#print axioms Pending.tail_smaller
#print axioms drain_transcript
end J6R25PreparedSupply


