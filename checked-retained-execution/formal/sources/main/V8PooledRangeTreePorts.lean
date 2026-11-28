import V8PooledRangeSpine

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace V8PooledRange

/-- Edge labels with their actual endpoints in the C5 caterpillar. -/
def privateLeafEdge : (k : ℕ) → Fin (k+1) → TreeEdge k
  | 0, _ => ()
  | k+1, i => Fin.cases (.inl false) (fun j => .inr (privateLeafEdge k j)) i

def neighboringSpineEdge : (k : ℕ) → Fin k → TreeEdge k
  | 0, i => i.elim0
  | k+1, i => Fin.cases (.inl true) (fun j => .inr (neighboringSpineEdge k j)) i

def treeEdgeKind : (k : ℕ) → TreeEdge k → Fin (k+1) ⊕ Fin k
  | 0, _ => .inl 0
  | _+1, .inl false => .inl 0
  | _+1, .inl true => .inr 0
  | k+1, .inr e => (treeEdgeKind k e).map Fin.succ Fin.succ

@[simp] theorem treeEdgeKind_leaf (k : ℕ) (i : Fin (k+1)) :
    treeEdgeKind k (privateLeafEdge k i) = .inl i := by
  induction k with
  | zero => rw [Fin.eq_zero i]; rfl
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (treeEdgeKind k (privateLeafEdge k j)).map Fin.succ Fin.succ = .inl j.succ
      rw [ih]
      rfl

@[simp] theorem treeEdgeKind_spine (k : ℕ) (i : Fin k) :
    treeEdgeKind k (neighboringSpineEdge k i) = .inr i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (treeEdgeKind k (neighboringSpineEdge k j)).map Fin.succ Fin.succ = .inr j.succ
      rw [ih]
      rfl

theorem treeEdge_ofKind (k : ℕ) (i : TreeEdge k) :
    (treeEdgeKind k i).elim (privateLeafEdge k) (neighboringSpineEdge k) = i := by
  induction k with
  | zero => cases (show Unit from i); rfl
  | succ k ih =>
    change Bool ⊕ TreeEdge k at i
    cases i with
    | inl c => cases c <;> rfl
    | inr j =>
      specialize ih j
      change ((treeEdgeKind k j).map Fin.succ Fin.succ).elim
        (privateLeafEdge (k+1)) (neighboringSpineEdge (k+1)) = Sum.inr j
      rcases h : treeEdgeKind k j with (a | a)
      · change Sum.inr (privateLeafEdge k a) = Sum.inr j
        exact congrArg Sum.inr (by simpa only [h,Sum.elim_inl] using ih)
      · change Sum.inr (neighboringSpineEdge k a) = Sum.inr j
        exact congrArg Sum.inr (by simpa only [h,Sum.elim_inr] using ih)

def treeEdgesEquiv (k : ℕ) : TreeEdge k ≃ Fin (k+1) ⊕ Fin k where
  toFun := treeEdgeKind k
  invFun i := i.elim (privateLeafEdge k) (neighboringSpineEdge k)
  left_inv := treeEdge_ofKind k
  right_inv i := by cases i <;> simp

@[simp] theorem treeEnd_leaf (k : ℕ) (i : Fin (k+1)) (b : Bool) :
    treeEnds k (privateLeafEdge k i) b = (i,b) := by
  induction k with
  | zero => rw [Fin.eq_zero i]; rfl
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change ((treeEnds k (privateLeafEdge k j) b).1.succ,
        (treeEnds k (privateLeafEdge k j) b).2) = (j.succ,b)
      rw [ih]

@[simp] theorem treeEnd_spine (k : ℕ) (i : Fin k) (b : Bool) :
    treeEnds k (neighboringSpineEdge k i) b = ((if b then i.succ else i.castSucc),false) := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b <;> rfl
    · change ((treeEnds k (neighboringSpineEdge k j) b).1.succ,
        (treeEnds k (neighboringSpineEdge k j) b).2) = ((if b then j.succ.succ else j.succ.castSucc),false)
      rw [ih]
      cases b
      · rfl
      · rfl

/-- Two deficit tokens per private leaf and one per end of the spine. -/
abbrev Deficit (k : ℕ) := (Fin (k+1) × Bool) ⊕ Bool

def deficitTarget (k : ℕ) : Deficit k → Tree k
  | .inl (i,_) => (i,true)
  | .inr b => ((if b then Fin.last k else 0),false)

abbrev TreeToken (k : ℕ) := ((Fin (k+1) × Bool) ⊕ (Fin k × Bool)) ⊕ Deficit k

def openTreeHalf (k : ℕ) : TreeToken k → Tree k × Fin 3
  | .inl (.inl (i,b)) => ((i,b),0)
  | .inl (.inr (i,b)) => if b then ((i.succ,false),1) else ((i.castSucc,false),2)
  | .inr (.inl (i,b)) => ((i,true),if b then 2 else 1)
  | .inr (.inr b) => (deficitTarget k (.inr b),if b then 2 else 1)

def treeSlot1 (k : ℕ) (v : Tree k) : TreeToken k :=
  if v.2 then .inr (.inl (v.1,false))
  else if h : 0 < v.1.val then
    .inl (.inr (⟨v.1.val-1, by have hv := v.1.isLt; omega⟩,true))
  else .inr (.inr false)

def treeSlot2 (k : ℕ) (v : Tree k) : TreeToken k :=
  if v.2 then .inr (.inl (v.1,true))
  else if h : v.1.val < k then .inl (.inr (⟨v.1.val,h⟩,false))
  else .inr (.inr true)

def closeTreeHalf (k : ℕ) (q : Tree k × Fin 3) : TreeToken k :=
  Fin.cases (.inl (.inl q.1)) (fun i => Fin.cases (treeSlot1 k q.1) (fun _ => treeSlot2 k q.1) i) q.2

@[simp] theorem closeTreeHalf_0 (k : ℕ) (v : Tree k) :
    closeTreeHalf k (v,0) = .inl (.inl v) := rfl
@[simp] theorem closeTreeHalf_1 (k : ℕ) (v : Tree k) :
    closeTreeHalf k (v,1) = treeSlot1 k v := rfl
@[simp] theorem closeTreeHalf_2 (k : ℕ) (v : Tree k) :
    closeTreeHalf k (v,2) = treeSlot2 k v := rfl

theorem close_openTreeHalf (k : ℕ) (q : TreeToken k) :
    closeTreeHalf k (openTreeHalf k q) = q := by
  rcases q with ((⟨i,b⟩ | ⟨i,b⟩) | (⟨i,b⟩ | b))
  · rfl
  · cases b
    · have hi : i.val < k := i.isLt
      simp [openTreeHalf,treeSlot2,hi]
    · simp [openTreeHalf,treeSlot1]
  · cases b <;> rfl
  · cases b <;> simp [openTreeHalf,deficitTarget,treeSlot1,treeSlot2]

theorem open_closeTreeHalf (k : ℕ) (q : Tree k × Fin 3) :
    openTreeHalf k (closeTreeHalf k q) = q := by
  rcases q with ⟨⟨i,l⟩,j⟩
  fin_cases j
  · rfl
  · change openTreeHalf k (closeTreeHalf k ((i,l),1)) = ((i,l),1)
    rw [closeTreeHalf_1]
    cases l
    · by_cases hi : 0 < i.val
      · have hsmall : i.val-1 < k := by have hv := i.isLt; omega
        have hsucc : (⟨i.val-1,hsmall⟩ : Fin k).succ = i := by
          apply Fin.ext
          change i.val-1+1 = i.val
          omega
        simp [treeSlot1,hi,openTreeHalf,hsucc]
      · have hzero : i = 0 := Fin.ext (by simpa using (Nat.eq_zero_of_not_pos hi))
        subst i
        simp [treeSlot1,openTreeHalf,deficitTarget]
    · rfl
  · change openTreeHalf k (closeTreeHalf k ((i,l),2)) = ((i,l),2)
    rw [closeTreeHalf_2]
    cases l
    · by_cases hi : i.val < k
      · simp [treeSlot2,hi,openTreeHalf]
      · have heq : i = Fin.last k := Fin.ext (by have hv := i.isLt; simp; omega)
        subst i
        simp [treeSlot2,openTreeHalf,deficitTarget]
    · rfl

def treeSocketEquiv (k : ℕ) : TreeToken k ≃ Tree k × Fin 3 where
  toFun := openTreeHalf k
  invFun := closeTreeHalf k
  left_inv := close_openTreeHalf k
  right_inv := open_closeTreeHalf k

#print axioms treeEdgesEquiv
#print axioms treeEnd_leaf
#print axioms treeEnd_spine
#print axioms treeSocketEquiv

end V8PooledRange
