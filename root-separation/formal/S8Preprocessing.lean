import S8PlacementSampling

namespace S8

open scoped BigOperators

variable {I P A : Type*} [Fintype I] [Fintype A] [DecidableEq P]

/-- The agreement indicator of two full ordered cells reads at most four
    words' primitive positions. Tied positions are counted only once. -/
def agreementSupport (left right : Bool × I → P) : Finset P :=
  (Finset.univ.image left) ∪ (Finset.univ.image right)

theorem agreementSupport_card (left right : Bool × I → P) :
    (agreementSupport left right).card ≤ 4 * Fintype.card I := by
  have hleft : (Finset.univ.image left).card ≤ Fintype.card (Bool × I) := Finset.card_image_le.trans_eq rfl
  have hright : (Finset.univ.image right).card ≤ Fintype.card (Bool × I) := Finset.card_image_le.trans_eq rfl
  have hs := (Finset.card_union_le (Finset.univ.image left) (Finset.univ.image right)).trans
    (Nat.add_le_add hleft hright)
  simpa only [agreementSupport] using
    (hs.trans_eq (by simp [Fintype.card_prod]; omega))

omit [Fintype A] in
theorem support_preserves_agreement (left right : Bool × I → P) (x y : P → A)
    (same : ∀ p ∈ agreementSupport left right, x p = y p) :
    (x ∘ left = x ∘ right) ↔ (y ∘ left = y ∘ right) := by
  have l : x ∘ left = y ∘ left := by
    funext i
    exact same _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have r : x ∘ right = y ∘ right := by
    funext i
    exact same _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  rw [l,r]

/-- Enumeration bound for one conditional agreement query. This counts possible
    assignments to its entire support, and so also bounds any partial fixing. -/
theorem support_enumeration_bound [Nonempty A] (left right : Bool × I → P) :
    Fintype.card (agreementSupport left right → A) ≤
      Fintype.card A ^ (4 * Fintype.card I) := by
  rw [Fintype.card_fun, Fintype.card_coe]
  exact Nat.pow_le_pow_right Fintype.card_pos (agreementSupport_card left right)

#print axioms agreementSupport_card
#print axioms support_preserves_agreement
#print axioms support_enumeration_bound

end S8

