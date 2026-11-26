
import MainProbe
import PrecisionErasure
import QueryBounds

namespace NativeJ2
open scoped Polynomial
open MainProbe

universe u v w c

variable {I : Type u} {S : Type v} {X : Type w} {Copy : Type c}
  [Fintype I] [DecidableEq I] [DecidableEq S] [Fintype S]

/-- A common root address supplies the private-point fibre, Taylor direction,
    and fixed diagonal coordinates. Its non-pin factors may depend on the input. -/
structure Address (I S X : Type*) (k : ℕ) where
  node : I
  fixed : Fin k → Bool
  fibre : S → Finset (X → Bool)
  direction : X → Bool
  other : (Fin k → Bool) → Bool → S → (X → Bool) → ℚ[X]

variable {R O : Type*} [CommSemiring R] [CommSemiring O]

/-- The lower bound composes actual MAIN fibre support and D precision erasure.
    The source-packing certificate must separately furnish abundance and D's
    coefficient structure for the chosen physical instance. -/
theorem mixed_of_native_registers {k k₀ : ℕ} {D : Type*}
    (layout : DiagonalLayout I S X Copy (Fin k))
    (interval : Finset ℕ) (hOutside : 0 ∉ interval) (f : ℚ[X]) (node : I → ℚ)
    (abundance : ∀ t g, k₀ ≤ (ownedPins layout t g Finset.univ).card)
    (ψ : R →+* O) (precision : ℕ) (hprecision : (2 : O) ^ precision = 0)
    (p : (Fin k → Bool) → Bool → D → R[X]) (z : D → O)
    (targets ord : D → ℕ)
    (hord : ∀ d, targets d ≤ ord d)
    (hcoeff : ∀ s b d j, (2 : R) ^ (precision - targets d - j) ∣ (p s b d).coeff j)
    (tree : FiniteWeightedQueryTree.DecisionTree
      (Address I S X k ⊕ (Address I S X k × S) ⊕ D) (ℚ[X] × O))
    (correct : ∀ s b, FiniteWeightedQueryTree.evaluate (fun q =>
      match q with
      | .inl a => (sourceCompletedProbe layout interval f node a.node Finset.univ
          a.fibre a.direction a.fixed s (a.other s b), 0)
      | .inr (.inl (a,g)) => (sourceGroupProbe layout interval f node a.node g Finset.univ
          (a.fibre g) a.direction a.fixed s (a.other s b g), 0)
      | .inr (.inr d) => (0,
          (2 : O) ^ ord d * z d ^ targets d * (p s b d).eval₂ ψ (2 * z d))) tree = b) :
    ∃ s b, 2 ^ k ≤ FiniteWeightedQueryTree.paid
      (Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2 ^ (k-k₀)) (fun _ => 0)))
      (fun q =>
      match q with
      | .inl a => (sourceCompletedProbe layout interval f node a.node Finset.univ
          a.fibre a.direction a.fixed s (a.other s b), 0)
      | .inr (.inl (a,g)) => (sourceGroupProbe layout interval f node a.node g Finset.univ
          (a.fibre g) a.direction a.fixed s (a.other s b g), 0)
      | .inr (.inr d) => (0,
          (2 : O) ^ ord d * z d ^ targets d * (p s b d).eval₂ ψ (2 * z d))) tree := by
  classical
  apply FiniteWeightedQueryTree.mixed_actual_path 0 _ (fun a => pinCylinder Finset.univ a.fixed)
    (fun a => pinCylinder (ownedPins layout a.1.node a.2 Finset.univ) a.1.fixed)
    _ _ _ _ _ tree correct
  · intro a
    simp [pinCylinder_card]
  · rintro ⟨a,g⟩
    rw [pinCylinder_card, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left (abundance a.node g) k)
  · intro s b a hs
    change (_, (0:O)) = (0,0)
    rw [sourceCompletedProbe_outside_cylinder layout interval hOutside f node a.node
      Finset.univ a.fibre a.direction a.fixed s (a.other s b) hs]
  · rintro s b ⟨a,g⟩ hs
    change (_, (0:O)) = (0,0)
    rw [sourceGroupProbe_outside_cylinder layout interval hOutside f node a.node g
      Finset.univ (a.fibre g) a.direction a.fixed s (a.other s b g) hs]
  · intro s b d
    have h := PrecisionErasure.every_slot_erased ψ (p s b d) (z d) precision
      (targets d) (ord d) (hord d) (hcoeff s b d)
    rw [hprecision, zero_dvd_iff] at h
    exact Prod.ext rfl h

#print axioms mixed_of_native_registers
end NativeJ2


