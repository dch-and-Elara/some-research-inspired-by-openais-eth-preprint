import P5HybridClosureAffineLayout

/-! An optional fixed scalar offset is one genuine entrance in the
same whole-coordinate group-product model, not a new free operation. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open GroupProducts

variable {V I A T K : Type*} [Fintype A] [Fintype T] [Field K]

def constantGroupTerm (L : V→I→A) (i : I) (c : K) : GroupTerm L K where
  coordinate := i
  coeff := c
  factor := fun _ _=>1

omit [Fintype T] in
theorem constant_group_value (L : V→I→A) (i : I) (c : K) (σ : V→Bool) :
    (constantGroupTerm L i c).value σ=c := by
  simp [constantGroupTerm,GroupTerm.value]

def includeOffset {L : V→I→A} (terms : T→GroupTerm L K) (i : I) (c : K) :
    (Unit⊕T)→GroupTerm L K := Sum.elim (fun _=>constantGroupTerm L i c) terms

theorem includeOffset_value {L : V→I→A} (terms : T→GroupTerm L K) (i : I) (c : K) (σ : V→Bool) :
    (∑ t : Unit⊕T,(includeOffset terms i c t).value σ) =
      c+∑ t,(terms t).value σ := by
  rw [Fintype.sum_sum_type]
  simp [includeOffset,constant_group_value]

theorem includeOffset_one_extra : Fintype.card (Unit⊕T)=Fintype.card T+1 := by
  simp [Nat.add_comm]

#print axioms constant_group_value
#print axioms includeOffset_value
#print axioms includeOffset_one_extra
end Paper5.HybridClosure