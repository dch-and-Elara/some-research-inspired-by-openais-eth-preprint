import J6R15ModeCostStep

/-! A conservative materialization envelope for the state. Each suffix
word and each budget/counter/weight receives a q-bit field; an extra
bit per field plus boundary fields covers its delimiter/control tags.
Even copying full states avoids any free-mapping or RAM assumption. -/
namespace J6R15ModeCost

def stackWords {q : ℕ} : List (Frame q)→ℕ
  | [] => 0
  | f::fs => f.pending.length+4+stackWords fs

def stateWords {q : ℕ} : State q→ℕ
  | .enter ws _ fs => ws.length+2+stackWords fs
  | .ascend fs => 1+stackWords fs

theorem stackWords_bound {q n : ℕ} (fs : List (Frame q)) (hf : StackShape n fs) :
    stackWords fs≤fs.length*(n+3) := by
  induction fs with
  | nil => simp [stackWords]
  | cons f fs ih =>
    obtain ⟨hp,hs⟩ := hf
    have h := ih hs
    simp only [List.length_cons] at hp
    change f.pending.length+4+stackWords fs≤(fs.length+1)*(n+3)
    rw [Nat.succ_mul]
    omega

theorem stateWords_bound {q n : ℕ} (s : State q) (h : s.wellFormed n) :
    stateWords s≤(n+2)^2 := by
  cases s with
  | enter ws K fs =>
    obtain ⟨hN,hshape⟩ := h
    have H := stackWords_bound fs hshape
    have hFS : fs.length≤n := by omega
    have hW : ws.length≤n := by omega
    have hv := Nat.mul_le_mul_right (n+3) hFS
    change ws.length+2+stackWords fs≤_
    nlinarith
  | ascend fs =>
    obtain ⟨hN,hshape⟩ := h
    have H := stackWords_bound fs hshape
    have hv := Nat.mul_le_mul_right (n+3) hN
    change 1+stackWords fs≤_
    nlinarith

theorem scan_budget_covers {q n : ℕ} (s t : State q)
    (hs : s.wellFormed n) (ht : t.wellFormed n) :
    (4*stateWords s+4*stateWords t+4*n+8)*(q+1)≤scanCap q n := by
  have hS := stateWords_bound s hs
  have hT := stateWords_bound t ht
  unfold scanCap
  apply Nat.mul_le_mul_right
  nlinarith

#print axioms stackWords_bound
#print axioms stateWords_bound
#print axioms scan_budget_covers
end J6R15ModeCost

