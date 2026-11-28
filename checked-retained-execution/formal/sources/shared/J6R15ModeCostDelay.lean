import J6R15ModeCostStep

/-! Watchdog semantics. The fuel is a proof-side limit on silent
transitions, not an additional machine field. Each invocation returns
one emitted tuple or halts; it cannot build a sibling list in advance. -/
namespace J6R15ModeCost
open AOracleMachineTime

inductive Ready {q : ℕ} (n : ℕ) : Pulse q→Prop
  | halt : Ready n .halt
  | emitted (ws : List (Word q)) (s : State q) :
      ws.length=n → s.wellFormed n → Ready n (.emit ws s)

def untilEvent {q : ℕ} (n : ℕ) : ℕ → State q → Meter (Pulse q)
  | 0,s => ⟨.again s,0⟩
  | k+1,s =>
    let t := step n s
    match t.result with
    | .again s' =>
      let r := untilEvent n k s'
      ⟨r.result,t.steps+r.steps⟩
    | .emit _ _ => t
    | .halt => t

theorem untilEvent_cost {q : ℕ} (n k : ℕ) (s : State q) :
    (untilEvent n k s).steps≤k*transitionCap q n := by
  induction k generalizing s with
  | zero => simp [untilEvent]
  | succ k ih =>
    have h := step_bound n s
    rw [Nat.succ_mul]
    cases ht : (step n s).result with
    | again t =>
      simp only [untilEvent,ht]
      exact Nat.add_le_add h (ih t) |>.trans_eq (Nat.add_comm _ _)
    | emit w t =>
      simp only [untilEvent,ht]
      exact h.trans (Nat.le_add_left _ _)
    | halt =>
      simp only [untilEvent,ht]
      exact h.trans (Nat.le_add_left _ _)

theorem untilEvent_progress {q n : ℕ} (k : ℕ) (s : State q) (hS : s.wellFormed n)
    (hk : quietRank n s≤k) :
    Ready n (untilEvent n k s).result := by
  induction k generalizing s with
  | zero => have := quietRank_pos n s; omega
  | succ k ih =>
    cases ht : (step n s).result with
    | again t =>
      obtain ⟨hw,hR⟩ := step_silent s t hS ht
      simpa only [untilEvent,ht] using ih t hw (by omega)
    | emit w t =>
      obtain ⟨hw,hl⟩ := step_emit s t w hS ht
      simpa only [untilEvent,ht] using Ready.emitted w t hl hw
    | halt =>
      simpa only [untilEvent,ht] using (Ready.halt (n:=n) (q:=q))

theorem paid_delay {q n : ℕ} (s : State q) (hs : s.wellFormed n) :
    let R := untilEvent n (2*n+1) s
    Ready n R.result ∧ R.steps≤(2*n+1)*transitionCap q n :=
  ⟨untilEvent_progress _ s hs (quietRank_bound s hs),untilEvent_cost _ _ _⟩

def start {q : ℕ} (ws : List (Word q)) (p : Word q) : Meter (Pulse q) :=
  let r := subtract p (word 1)
  ⟨if r.result.2 then .halt else .again (.enter ws r.result.1 []),
    r.steps+4*(ws.length+1)*(q+1)+8⟩

theorem start_exact {q : ℕ} (hq : 0<q) (ws : List (Word q)) (p : Word q) :
    let t := start ws p
    ((t.result=.halt ↔ p.val=0) ∧
      (p.val≠0 → ∃ r : Word q, r.val=p.val-1 ∧ t.result=.again (.enter ws r []))) ∧
    t.steps≤16*q+14+4*(ws.length+1)*(q+1) := by
  let r := subtract p (word 1)
  have h1 : (word (q:=q) 1).val=1 := word_val (one_lt_pow₀ (by decide) hq.ne')
  obtain ⟨hs,hV,hC⟩ := subtract_exact p (word 1)
  change (r.result.2=false ↔ _) at hs
  change (r.result.2=false → r.result.1.val=_) at hV
  rw [h1] at hs hV
  refine ⟨?_,?_⟩
  · change (((if r.result.2 then .halt else .again (.enter ws r.result.1 [])) : Pulse q)=.halt ↔ _) ∧ _
    cases hb : r.result.2 with
    | true =>
      have h0 : p.val=0 := by
        have h : ¬1≤p.val := by simpa [hb] using hs
        omega
      simp [h0]
    | false =>
      have hp : 1≤p.val := hs.mp hb
      refine ⟨by simp [show p.val≠0 by omega],?_⟩
      intro _
      refine ⟨r.result.1,hV hb,?_⟩
      change (if r.result.2 then Pulse.halt else Pulse.again (.enter ws r.result.1 []))=_
      rw [hb]
      rfl
  · change r.steps+4*(ws.length+1)*(q+1)+8≤_
    rw [show r.steps=_ from hC]
    omega

#print axioms untilEvent_cost
#print axioms untilEvent_progress
#print axioms paid_delay
#print axioms start_exact
end J6R15ModeCost




