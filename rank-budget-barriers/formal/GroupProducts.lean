import BalancedUnion
import SeparatedRank

/-! Regrouping the original symbol-local factors into two functions, with
the actual vertex input types of SeparatedRank.VertexTerm. -/

namespace GroupProducts

open scoped BigOperators

variable {V I A K : Type*}

/-- A coefficient times the product of one arbitrary function for every
symbol of the term's chosen coordinate. -/
structure GroupTerm (L : V → I → A) (K : Type*) where
  coordinate : I
  coeff : K
  factor : ∀ a : A, ({v : V // L v coordinate = a} → Bool) → K

namespace GroupTerm

variable {L : V → I → A} (t : GroupTerm L K)

def value [Fintype A] [CommMonoid K] (σ : V → Bool) : K :=
  t.coeff * ∏ a, t.factor a (fun v => σ v.1)

variable [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

/-- A union of whole symbols determines both the vertex cut and the two
functions. The type of each function exposes only vertices on its own side. -/
def toVertexTerm [CommMonoid K] (symbols : I → Finset A) : SeparatedRank.VertexTerm V K where
  side := EmpiricalCutMoments.labelCut L id symbols t.coordinate
  coeff := t.coeff
  onCut x := BalancedUnion.localProduct (fun v => L v t.coordinate) t.factor (symbols t.coordinate)
    (fun v => x ⟨v.1, by simpa [EmpiricalCutMoments.labelCut] using v.2⟩)
  offCut x := BalancedUnion.localProduct (fun v => L v t.coordinate) t.factor
    ((symbols t.coordinate)ᶜ) (fun v => x ⟨v.1, by
      simpa [EmpiricalCutMoments.labelCut] using v.2⟩)

theorem toVertexTerm_side [CommMonoid K] (symbols : I → Finset A) :
    (t.toVertexTerm symbols).side = EmpiricalCutMoments.labelCut L id symbols t.coordinate := rfl

theorem toVertexTerm_value [Field K] (symbols : I → Finset A) (σ : V → Bool) :
    (t.toVertexTerm symbols).value σ = t.value σ := by
  change t.coeff *
      BalancedUnion.localProduct (fun v => L v t.coordinate) t.factor (symbols t.coordinate)
        (fun v => σ v.1) *
      BalancedUnion.localProduct (fun v => L v t.coordinate) t.factor ((symbols t.coordinate)ᶜ)
        (fun v => σ v.1) =
    t.coeff * ∏ a, t.factor a (fun v => σ v.1)
  rw [BalancedUnion.group_product_separates (fun v => L v t.coordinate) t.factor
    (symbols t.coordinate) σ, mul_assoc]

end GroupTerm

variable [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

theorem sum_toVertexTerm_values [Field K] {T : Type*} [Fintype T] {L : V → I → A}
    (terms : T → GroupTerm L K) (symbols : I → Finset A) (σ : V → Bool) :
    (∑ t, ((terms t).toVertexTerm symbols).value σ) = ∑ t, (terms t).value σ :=
  Finset.sum_congr rfl fun t _ => (terms t).toVertexTerm_value symbols σ

/-- The source supplies one balanced vertex union per used coordinate.
Every group term then becomes a separated term on its own coordinate's union
with the same pointwise value and the same coefficient. -/
theorem source_balanced_views [Nonempty V] [Fintype I] [DecidableEq I] [Field K]
    {P T : Type*} [Fintype P] (pin : V ↪ P) (cell : P → (I → A) × (I → A)) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate cell Δ) (hports : Fintype.card P = 10 * Fintype.card V)
    (hA : 27 ≤ Fintype.card A) (kept : Finset I)
    (terms : T → GroupTerm (fun v => SourceDensity.firstCoordinates kept (cell (pin v))) K) :
    let L := fun v => SourceDensity.firstCoordinates kept (cell (pin v))
    ∃ symbols : kept → Finset A,
      (∀ i, (1 / 4 : ℚ) * Fintype.card V ≤
        (min (EmpiricalCutMoments.labelCut L id symbols i).card
          (Fintype.card V - (EmpiricalCutMoments.labelCut L id symbols i).card) : ℕ)) ∧
      (∀ t, ((terms t).toVertexTerm symbols).side =
        EmpiricalCutMoments.labelCut L id symbols (terms t).coordinate) ∧
      (∀ t σ, ((terms t).toVertexTerm symbols).value σ = (terms t).value σ) := by
  obtain ⟨allSymbols, hbalance⟩ := BalancedUnion.source_balanced_unions pin cell Δ cert hports hA
  exact ⟨fun i => allSymbols i.1, fun i => hbalance i.1,
    fun t => (terms t).toVertexTerm_side _, fun t => (terms t).toVertexTerm_value _⟩

#print axioms GroupTerm.toVertexTerm_side
#print axioms GroupTerm.toVertexTerm_value
#print axioms sum_toVertexTerm_values
#print axioms source_balanced_views

end GroupProducts
