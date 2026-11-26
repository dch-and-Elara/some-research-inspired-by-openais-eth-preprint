import J6R10ReachablePadding

/-! The dependent mode alphabet may be reindexed by a genuine
weight-preserving bijection. The legal weighted menu is preserved
with the actual Finsupp exponent tuple, not just its cardinality. -/
namespace J6R12Integral
open scoped Classical
open J6R10Reachable

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem paddedWeight_equiv (p : ℕ) (e : I ≃ J) (w : I → ℕ) (v : J → ℕ)
    (weightMatch : ∀ i, v (e i) = w i) :
    paddedWeight p e.toEmbedding w = v := by
  funext j
  obtain ⟨i,rfl⟩ := e.surjective j
  exact (paddedWeight_hit p e.toEmbedding w i).trans (weightMatch i).symm

noncomputable def menuReindex (p : ℕ) (hp : 0 < p) (e : I ≃ J)
    (w : I → ℕ) (v : J → ℕ) (hw : ∀ i, 0 < w i) (weightMatch : ∀ i, v (e i) = w i) :
    Menu p w ≃ Menu p v :=
  (menuEquiv p hp e.toEmbedding w hw).trans <|
    Equiv.subtypeEquivRight (fun _ => by rw [paddedWeight_equiv p e w v weightMatch])

theorem menuReindex_val (p : ℕ) (hp : 0 < p) (e : I ≃ J)
    (w : I → ℕ) (v : J → ℕ) (hw : ∀ i, 0 < w i)
    (weightMatch : ∀ i, v (e i) = w i) (β : Menu p w) :
    (menuReindex p hp e w v hw weightMatch β).val = Finsupp.embDomain e.toEmbedding β.val := rfl

#print axioms paddedWeight_equiv
#print axioms menuReindex_val
end J6R12Integral
