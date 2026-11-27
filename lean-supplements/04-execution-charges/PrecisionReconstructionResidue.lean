import RetunedLayout
import MenuBounds
import IntegralOutputTransfer

/-! Section 6's arbitrary correct-residue lift, with no requirement that
the exactly reconstructed integral value equal the natural count itself. -/

namespace IntegralOutputTransfer

open scoped BigOperators

variable {X U R S K : Type*} [Fintype U] [CommRing R] [CommRing S] [CommRing K]

/-- The concrete output supplied by the precision identity. -/
def familyLift (varpi : R) (p : ℕ) (target : X → R) (cleared error : U → X → R) :
    X → R :=
  fun x => target x + varpi ^ p * ∑ u, cleared u x * error u x

/-- Both the exact lifted identity and correctness modulo the residue map
hold for every input, including arbitrary exact targets with the right residue. -/
theorem family_lift_contract
    (embed : R →+* K) (residue : R →+* S) (varpi : R) (p : ℕ)
    (q : U → ℕ) (coefficient : U → K)
    (original replacement cleared error : U → X → R) (target : X → R)
    (herr : ∀ u x, replacement u x = original u x + varpi ^ q u * error u x)
    (hclear : ∀ u x, coefficient u * embed (varpi ^ q u) = embed (varpi ^ p * cleared u x))
    (hexact : ∀ x, (∑ u, coefficient u * embed (original u x)) = embed (target x))
    (hvarpi : residue varpi = 0) (hp : 0 < p) :
    (∀ x, (∑ u, coefficient u * embed (replacement u x)) =
      embed (familyLift varpi p target cleared error x)) ∧
    (∀ x, residue (familyLift varpi p target cleared error x) = residue (target x)) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact weighted_lift_identity embed varpi p q (fun u => original u x)
      (fun u => replacement u x) coefficient (fun u => cleared u x) (fun u => error u x)
      (target x) (fun u => herr u x) (fun u => hclear u x) (hexact x)
  · intro x
    exact reconstructed_residue residue varpi (target x) (∑ u, cleared u x * error u x)
      p hvarpi hp

#print axioms family_lift_contract

end IntegralOutputTransfer

namespace ExpanderBarrier

open scoped BigOperators

variable {V I A J T U R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype J] [Fintype T] [Fintype U]
variable [CommRing R] [CommRing S] [Nontrivial S] [Field K]
variable {E : Finset (V × V)} {L : V → I → A} {owner : J → I} {symbols : J → Finset A}

/-- Compose the correct-residue identity with the actual common-matching
barrier. No term must separately lift integrally. -/
theorem reconstructed_output_barrier_of_residue (G : LabelGeometry E L owner symbols)
    (d : ℕ) (hd : (d : ℚ) ≤ margin G) (hbudget : SelectionBudget G)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (varpi : R) (p : ℕ) (q : U → ℕ) (coefficient : U → K)
    (original replacement cleared error : U → (V → Bool) → R) (target : (V → Bool) → R)
    (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ t, (terms t).side = EmpiricalCutMoments.labelCut L owner symbols (assigned t))
    (herr : ∀ u σ, replacement u σ = original u σ + varpi ^ q u * error u σ)
    (hclear : ∀ u σ, coefficient u * embed (varpi ^ q u) = embed (varpi ^ p * cleared u σ))
    (hexact : ∀ σ, (∑ u, coefficient u * embed (original u σ)) = embed (target σ))
    (hrepresentation : ∀ σ, (∑ u, coefficient u * embed (replacement u σ)) =
      ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (target σ) = (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (hvarpi : residue varpi = 0) (hp : 0 < p) :
    2 ^ d ≤ Fintype.card T := by
  obtain ⟨hlift, hres⟩ := IntegralOutputTransfer.family_lift_contract embed residue varpi p q
    coefficient original replacement cleared error target herr hclear hexact hvarpi hp
  exact modular_output_barrier G d hd hbudget embed residue hinjective
    (IntegralOutputTransfer.familyLift varpi p target cleared error) terms assigned hside
    (fun σ => (hlift σ).symm.trans (hrepresentation σ)) (fun σ => (hres σ).trans (hcorrect σ))

#print axioms reconstructed_output_barrier_of_residue

end ExpanderBarrier

namespace RetunedLayout

open scoped BigOperators

variable {V P I A T U R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V] [Fintype P]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype T] [Fintype U] [CommRing R] [CommRing S] [Nontrivial S] [Field K]
variable {E : Finset (V × V)} {pin : V ↪ P}
variable {cell : P → (I → A) × (I → A)} {kept : Finset I}

/-- The exact finite Theorem 1 bound after separating the replacement
outputs, preserving the general correct-residue hypothesis of Section 6. -/
theorem reconstructed_output_barrier_of_residue (G : FullGroupBarrier.Layout E pin cell kept)
    (hN : LogarithmicBudget.cutoff
      (LogarithmicBudget.multiplier 1 80 (FiniteGrowth.coefficient G.gamma (1 / 4))) 0 ≤
      Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (varpi : R) (p : ℕ) (q : U → ℕ) (coefficient : U → K)
    (original replacement cleared error : U → (V → Bool) → R) (target : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (SourceBarrier.labels pin cell kept) K)
    (herr : ∀ u σ, replacement u σ = original u σ + varpi ^ q u * error u σ)
    (hclear : ∀ u σ, coefficient u * embed (varpi ^ q u) = embed (varpi ^ p * cleared u σ))
    (hexact : ∀ σ, (∑ u, coefficient u * embed (original u σ)) = embed (target σ))
    (hrepresentation : ∀ σ, (∑ u, coefficient u * embed (replacement u σ)) =
      ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (target σ) = (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (hvarpi : residue varpi = 0) (hp : 0 < p) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1 / 4) * Fintype.card V) ^ 2 ≤
      320 * ((Fintype.card V).log2 : ℚ) * (d : ℚ) ^ 2 ∧
      2 ^ d ≤ Fintype.card T := by
  obtain ⟨hlift, hres⟩ := IntegralOutputTransfer.family_lift_contract embed residue varpi p q
    coefficient original replacement cleared error target herr hclear hexact hvarpi hp
  exact modular_output_barrier G hN embed residue hinjective
    (IntegralOutputTransfer.familyLift varpi p target cleared error) terms
    (fun σ => (hlift σ).symm.trans (hrepresentation σ)) (fun σ => (hres σ).trans (hcorrect σ))

#print axioms reconstructed_output_barrier_of_residue

end RetunedLayout
