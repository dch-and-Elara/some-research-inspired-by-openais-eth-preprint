
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace PinnedWitness

variable {V : Type*} [DecidableEq V]

/-- A set of positive two-literal clauses evaluated at a common assignment. -/
def satisfied (E : Finset (V × V)) (x : V → Bool) : Prop :=
  ∀ e ∈ E, x e.1 = true ∨ x e.2 = true

def independentOn (E : Finset (V × V)) (P : Finset V) : Prop :=
  ∀ e ∈ E, ¬ (e.1 ∈ P ∧ e.2 ∈ P)

def enabled (P : Finset V) (w : V → Bool) (v : V) : Bool :=
  if v ∈ P then w v else true

def disabled (P : Finset V) (w : V → Bool) (p q v : V) : Bool :=
  if v = p ∨ v = q then false else enabled P w v

/-- J2 paired witnesses on the same diagonal word.  The exterior condition
    says any mate of a disabled triangle vertex lies outside P and is not disabled. -/
theorem paired (M D : Finset (V × V)) (P : Finset V) (p q : V) (w : V → Bool)
    (hI : independentOn (M ∪ D) P)
    (hM : (p,q) ∈ M) (hp : p ∉ P) (hq : q ∉ P)
    (hDL : ∀ e ∈ D, (e.1 = p ∨ e.1 = q) →
      e.2 ∉ P ∧ e.2 ≠ p ∧ e.2 ≠ q)
    (hDR : ∀ e ∈ D, (e.2 = p ∨ e.2 = q) →
      e.1 ∉ P ∧ e.1 ≠ p ∧ e.1 ≠ q) :
    let x₁ := enabled P w
    let x₀ := disabled P w p q
    (∀ v ∈ P, x₁ v = w v ∧ x₀ v = w v) ∧
    satisfied M x₁ ∧ satisfied D x₁ ∧ ¬ satisfied M x₀ ∧ satisfied D x₀ := by
  classical
  have hgood : satisfied (M ∪ D) (enabled P w) := by
    intro e he
    by_cases hl : e.1 ∈ P
    · have hr : e.2 ∉ P := fun hh => hI e he ⟨hl,hh⟩
      exact Or.inr (by simp [enabled, hr])
    · exact Or.inl (by simp [enabled, hl])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have h₁ : v ≠ p := fun h => hp (h ▸ hv)
    have h₂ : v ≠ q := fun h => hq (h ▸ hv)
    simp [enabled, disabled, hv, h₁, h₂]
  · exact fun e h => hgood e (Finset.mem_union_left _ h)
  · exact fun e h => hgood e (Finset.mem_union_right _ h)
  · intro bad
    have hf := bad (p,q) hM
    simp [disabled] at hf
  · intro e he
    by_cases hl : e.1 = p ∨ e.1 = q
    · obtain ⟨a,b,c⟩ := hDL e he hl
      exact Or.inr (by simp [disabled, enabled, a, b, c])
    · by_cases hr : e.2 = p ∨ e.2 = q
      · obtain ⟨a,b,c⟩ := hDR e he hr
        exact Or.inl (by simp [disabled, enabled, a, b, c])
      · simpa [disabled, hl, hr] using hgood e (Finset.mem_union_right _ he)

#print axioms paired
end PinnedWitness

