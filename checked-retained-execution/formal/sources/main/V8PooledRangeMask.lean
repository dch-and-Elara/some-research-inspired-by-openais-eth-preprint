import V8PooledRangeConclusion

set_option autoImplicit false
set_option warningAsError true

namespace V8PooledRange

theorem enabled_terminal (k : ℕ) (w : Word k) (b : Bool) :
    treeEnabled k w b (0,false) = b := by cases k <;> rfl

theorem enabled_other_spines (k : ℕ) (w : Word k) (b : Bool) (i : Fin k) :
    treeEnabled k w b (i.succ,false) = true := by
  induction k generalizing b with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change treeEnabled k (fun n => w n.succ) true (0,false) = true
      exact enabled_terminal _ _ _
    · change treeEnabled k (fun n => w n.succ) true (j.succ,false) = true
      exact ih _ true j

theorem enabled_base_leaf (k : ℕ) (w : Word k) (b : Bool) :
    treeEnabled k w b (Fin.last k,true) = true := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    have hi : (Fin.last k).succ = Fin.last (k+1) := by apply Fin.ext; rfl
    rw [← hi]
    exact ih (fun n => w n.succ) true

theorem enabled_word_leaves (k : ℕ) (w : Word k) (b : Bool) (i : Fin k) :
    treeEnabled k w b (i.castSucc,true) = w i := by
  induction k generalizing b with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change treeEnabled k (fun n => w n.succ) true (j.castSucc,true) = w j.succ
      exact ih _ true j

theorem enabled_core_off (k : ℕ) {O : Type*} (w : Word k) (b : Bool) (v : O) :
    hostEnabled k w b (.inr v) = false := rfl

/-- The availability switch is literally the sign of the second variable
in the same fixed physical clause, not an extra unit clause or a graph edit. -/
theorem switch_sign {V E : Type*} (G : Graph V E) (p : ThreePorts G)
    (s : V → Bool) (v : V) :
    (clauses G p s (.inl (.inr v))).2 = (.inl (v,2),s v) := rfl

#print axioms enabled_terminal
#print axioms enabled_other_spines
#print axioms enabled_base_leaf
#print axioms enabled_word_leaves
#print axioms enabled_core_off
#print axioms switch_sign

end V8PooledRange
