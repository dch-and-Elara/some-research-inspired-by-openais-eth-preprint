import J6R15ModeCostCursor

/-! A streaming DFS machine: one small transition at a time.
The stack stores literal suffixes instead of assuming pointer access.
The conservative frame envelope charges an entire read and copy of
the current bounded-size stack even when only its top is changed. -/
namespace J6R15ModeCost
open AOracleMachineTime

def zeroWord (q : ℕ) : Word q :=
  ⟨List.replicate q false,by simp⟩

theorem zeroWord_val (q : ℕ) : (zeroWord q).val=0 := by
  change bitsValue (List.replicate q false)=0
  induction q with
  | zero => rfl
  | succ r ih => simp [List.replicate_succ,bitsValue,ih]

structure Frame (q : ℕ) where
  weight : Word q
  pending : List (Word q)
  cursor : Cursor q

inductive State (q : ℕ) where
  | enter : List (Word q) → Word q → List (Frame q) → State q
  | ascend : List (Frame q) → State q

inductive Pulse (q : ℕ) where
  | again : State q → Pulse q
  | emit : List (Word q) → State q → Pulse q
  | halt : Pulse q

def scanCap (q n : ℕ) : ℕ := 16*(n+2)^2*(q+1)

def transitionCap (q n : ℕ) : ℕ := scanCap q n+(35*q+22)

def writeTuple {q : ℕ} (s : List (Frame q)) : List (Word q) :=
  s.reverse.map (fun f => f.cursor.counter)

def step {q : ℕ} (n : ℕ) : State q → Meter (Pulse q)
  | .enter [] _ fs => ⟨.emit (writeTuple fs) (.ascend fs),scanCap q n⟩
  | .enter (w::ws) K fs =>
    ⟨.again (.enter ws K (⟨w,ws,⟨K,zeroWord q⟩⟩::fs)),scanCap q n⟩
  | .ascend [] => ⟨.halt,scanCap q n⟩
  | .ascend (f::fs) =>
    let c := advance f.weight f.cursor
    let p := match c.result with
      | none => Pulse.again (.ascend fs)
      | some u => Pulse.again (.enter f.pending u.rem ({f with cursor := u}::fs))
    ⟨p,c.steps+scanCap q n⟩

def StackShape {q : ℕ} (n : ℕ) : List (Frame q) → Prop
  | [] => True
  | f::fs => f.pending.length+(f::fs).length=n ∧ StackShape n fs

def State.wellFormed {q : ℕ} (n : ℕ) : State q → Prop
  | .enter ws _ fs => ws.length+fs.length=n ∧ StackShape n fs
  | .ascend fs => fs.length≤n ∧ StackShape n fs

def quietRank {q : ℕ} (n : ℕ) : State q→ℕ
  | .enter ws _ _ => ws.length+1
  | .ascend fs => n+fs.length+1

theorem quietRank_pos {q : ℕ} (n : ℕ) (s : State q) : 0<quietRank n s := by
  cases s <;> simp [quietRank]

theorem quietRank_bound {q n : ℕ} (s : State q) (hs : s.wellFormed n) :
    quietRank n s≤2*n+1 := by
  cases s <;> simp only [State.wellFormed,quietRank] at * <;> omega

theorem step_bound {q : ℕ} (n : ℕ) (s : State q) :
    (step n s).steps≤transitionCap q n := by
  cases s with
  | enter ws K fs => cases ws <;> simp [step,transitionCap]
  | ascend fs =>
    cases fs with
    | nil => simp [step,transitionCap]
    | cons f fs =>
      change (advance f.weight f.cursor).steps+scanCap q n≤transitionCap q n
      unfold transitionCap
      have H := advance_bound f.weight f.cursor
      omega

theorem step_silent {q n : ℕ} (s t : State q) (hs : s.wellFormed n)
    (ht : (step n s).result=.again t) :
    t.wellFormed n ∧ quietRank n t<quietRank n s := by
  cases s with
  | enter ws K fs =>
    cases ws with
    | nil => simp [step] at ht
    | cons w ws =>
      simp only [step,Pulse.again.injEq] at ht
      subst t
      obtain ⟨hn,hf⟩ := hs
      have H : ws.length+(⟨w,ws,⟨K,zeroWord q⟩⟩::fs : List (Frame q)).length=n := by
        simp only [List.length_cons] at *
        omega
      exact ⟨⟨H,H,hf⟩,by simp [quietRank]⟩
  | ascend fs =>
    cases fs with
    | nil => simp [step] at ht
    | cons f fs =>
      have hs' := hs.1
      have hc : f.pending.length+(f::fs).length=n := hs.2.1
      have hl := hs.2.2
      cases h : (advance f.weight f.cursor).result with
      | none =>
        simp only [step,h,Pulse.again.injEq] at ht
        subst t
        refine ⟨⟨by simp only [List.length_cons] at hs'; omega,hl⟩,?_⟩
        simp [quietRank]
      | some u =>
        simp only [step,h,Pulse.again.injEq] at ht
        subst t
        refine ⟨⟨hc,hc,hl⟩,?_⟩
        simp only [quietRank,List.length_cons] at hc ⊢
        omega

theorem step_emit {q n : ℕ} (s t : State q) (ws : List (Word q))
    (hs : s.wellFormed n) (ht : (step n s).result=.emit ws t) :
    t.wellFormed n ∧ ws.length=n := by
  cases s with
  | enter rs K fs =>
    cases rs with
    | nil =>
      simp only [step,Pulse.emit.injEq] at ht
      obtain ⟨h₁,h₂⟩ := ht
      subst t
      subst ws
      simp only [State.wellFormed,List.length_nil,Nat.zero_add] at hs
      exact ⟨⟨hs.1.le,hs.2⟩,by rw [writeTuple,List.length_map,List.length_reverse,hs.1]⟩
    | cons r rs => simp [step] at ht
  | ascend fs =>
    cases fs with
    | nil => simp [step] at ht
    | cons f fs =>
      cases h : (advance f.weight f.cursor).result <;> simp [step,h] at ht

#print axioms quietRank_bound
#print axioms step_bound
#print axioms step_silent
#print axioms step_emit
end J6R15ModeCost


