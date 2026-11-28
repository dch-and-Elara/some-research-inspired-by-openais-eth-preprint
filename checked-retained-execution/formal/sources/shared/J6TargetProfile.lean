import J6ActiveProfile

/-! A fixed legal mode allocation contributes to exactly its target block.
This separates target packet/group multiplicities without moving old-variable
correlations between packets in the same group. -/
namespace J6TargetProfile
open scoped BigOperators Classical
open J6ActiveProfile

variable {I M K : Type*} [Fintype I] [Fintype M]

noncomputable def targetOccurrence {x : I→Option M} (block : I→K) (target : M→K)
    (owns : ∀ i m, x i=some m → block i=target m) (m : M) :
    {i : I // x i=some m} ≃ {j : {i : I // block i=target m} // x j.val=some m} where
  toFun i := ⟨⟨i.val,owns i.val m i.prop⟩,i.prop⟩
  invFun j := ⟨j.val.val,j.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype M] in
theorem target_count (x : I→Option M) (block : I→K) (target : M→K)
    (owns : ∀ i m, x i=some m → block i=target m) (m : M) :
    count x m = count (fun j : {i : I // block i=target m} => x j.val) m := by
  unfold count
  rw [← Fintype.card_subtype,← Fintype.card_subtype]
  exact Fintype.card_congr (targetOccurrence block target owns m)

omit [Fintype M] in
theorem profile_is_local (x : I→Option M) (block : I→K) (target : M→K)
    (owns : ∀ i m, x i=some m → block i=target m)
    (b : M → Fin (Fintype.card I+1)) :
    profile x=b ↔ ∀ m, count (fun j : {i : I // block i=target m} => x j.val) m = (b m).val := by
  constructor
  · intro h m
    rw [← target_count x block target owns m]
    exact congrArg (fun g : M→Fin (Fintype.card I+1) => (g m).val) h
  · intro h
    funext m
    apply Fin.ext
    change count x m = _
    rw [target_count x block target owns m,h m]

#print axioms target_count
#print axioms profile_is_local
end J6TargetProfile