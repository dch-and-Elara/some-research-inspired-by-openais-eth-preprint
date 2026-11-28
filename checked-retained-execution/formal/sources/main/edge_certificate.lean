import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Lean.Elab.Tactic.Omega

/-!
Two facts behind the variable-view support lower bound.
A product in a finite chain ring is nonzero exactly when the sum of its
truncated valuations is below the precision. The second theorem permits
each possible certificate to choose its own pivot edge and hence its own
coordinate chart on matched inputs.
-/

namespace NativeTwoView

theorem crossed_survival {p a b c d : Nat}
    (h₁ : a + b < p) (h₂ : c + d < p) :
    a + d < p ∨ c + b < p := by
  omega

theorem sound_fiber_unique {A : Type*} (p : Nat) (left right : A → Nat)
    (sound : ∀ x y, left x + right y < p → x = y)
    {x y : A} (hx : left x + right x < p) (hy : left y + right y < p) :
    x = y := by
  rcases crossed_survival hx hy with hr | hr
  · exact sound x y hr
  · exact (sound y x hr).symm

theorem cover_capacity {A C S T : Type*}
    [Fintype A] [Fintype C] [Fintype S] [Fintype T]
    (p : Nat) (chart : T → S ≃ C × A) (left right : T → C → A → Nat)
    (sound : ∀ t c x y, left t c x + right t c y < p → x = y)
    (cover : ∀ s, ∃ t,
      left t ((chart t s).1) ((chart t s).2) +
        right t ((chart t s).1) ((chart t s).2) < p) :
    Fintype.card S ≤ Fintype.card (T × C) := by
  classical
  choose pick hp using cover
  let encode (s : S) : T × C := (pick s, (chart (pick s) s).1)
  apply Fintype.card_le_of_injective encode
  intro s₁ s₂ he
  have ht : pick s₁ = pick s₂ := congrArg Prod.fst he
  have hc : (chart (pick s₁) s₁).1 = (chart (pick s₂) s₂).1 :=
    congrArg Prod.snd he
  rw [← ht] at hc
  have h₂ := hp s₂
  rw [← ht, ← hc] at h₂
  have ha := sound_fiber_unique p (left (pick s₁) ((chart (pick s₁) s₁).1))
    (right (pick s₁) ((chart (pick s₁) s₁).1))
    (sound (pick s₁) ((chart (pick s₁) s₁).1)) (hp s₁) h₂
  apply (chart (pick s₁)).injective
  exact Prod.ext hc ha

#print axioms crossed_survival
#print axioms sound_fiber_unique
#print axioms cover_capacity

end NativeTwoView
