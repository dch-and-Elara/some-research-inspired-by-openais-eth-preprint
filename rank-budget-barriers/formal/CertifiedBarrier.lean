import PinnedCNF
import SeparatedRank
import IntegralOutputTransfer

/-! The finite final-output theorem on genuine CNFs.
An induced matching is provided as a geometric witness, and its one endpoint
embedding must unbalance every actual cut used by a summand. The conclusion
is derived from CNF semantics, not from an assumed target rank. -/

namespace CertifiedBarrier

open scoped BigOperators

variable {V I J R S K : Type*}
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype J]
variable [CommRing R] [CommRing S] [Nontrivial S] [Field K]

theorem exact_count_barrier (E : Finset (V × V)) (matching : PinnedCNF.InducedMatching E I)
    (terms : J → SeparatedRank.VertexTerm V K)
    (hrepresentation : ∀ σ, (PinnedCNF.modelCount (PinnedCNF.formula E σ) : K) =
      ∑ j, (terms j).value σ)
    (d : ℕ)
    (hgap : ∀ j, d ≤ SeparatedRank.endpointImbalance matching.endpoint (terms j).side) :
    2 ^ d ≤ Fintype.card J := by
  apply SeparatedRank.vertex_barrier terms
    (fun σ => (PinnedCNF.modelCount (PinnedCNF.formula E σ) : K))
    hrepresentation matching.endpoint _ d hgap
  exact matching.countMatrix_rank K

theorem modular_output_barrier (E : Finset (V × V))
    (matching : PinnedCNF.InducedMatching E I)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R) (terms : J → SeparatedRank.VertexTerm V K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ j, (terms j).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (d : ℕ)
    (hgap : ∀ j, d ≤ SeparatedRank.endpointImbalance matching.endpoint (terms j).side) :
    2 ^ d ≤ Fintype.card J := by
  apply SeparatedRank.vertex_barrier terms (fun σ => embed (output σ))
    hrepresentation matching.endpoint _ d hgap
  let A : Matrix (I → Bool) (I → Bool) R :=
    fun x y => output (matching.restrictSigns x y)
  have hres : residue.mapMatrix A = matching.countMatrix S := by
    ext x y
    exact hcorrect (matching.restrictSigns x y)
  have hrank := IntegralOutputTransfer.full_rank_of_residue embed residue hinjective
    A (matching.countMatrix S) hres (matching.countMatrix_det_isUnit S).ne_zero
  simpa only [Fintype.card_fun, Fintype.card_bool] using hrank

theorem reconstructed_output_barrier {T : Type*} [Fintype T]
    (E : Finset (V × V)) (matching : PinnedCNF.InducedMatching E I)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (pi : R) (p : ℕ) (q : T → ℕ) (coefficient : T → K) (cleared : T → R)
    (original replacement error : T → (V → Bool) → R)
    (terms : J → SeparatedRank.VertexTerm V K)
    (herr : ∀ t σ, replacement t σ = original t σ + pi ^ q t * error t σ)
    (hclear : ∀ t, coefficient t * embed (pi ^ q t) = embed (pi ^ p * cleared t))
    (hexact : ∀ σ, (∑ t, coefficient t * embed (original t σ)) =
      embed (PinnedCNF.modelCount (PinnedCNF.formula E σ) : R))
    (hrepresentation : ∀ σ, (∑ t, coefficient t * embed (replacement t σ)) =
      ∑ j, (terms j).value σ)
    (hpi : residue pi = 0) (hp : 0 < p) (d : ℕ)
    (hgap : ∀ j, d ≤ SeparatedRank.endpointImbalance matching.endpoint (terms j).side) :
    2 ^ d ≤ Fintype.card J := by
  let output (σ : V → Bool) : R :=
    (PinnedCNF.modelCount (PinnedCNF.formula E σ) : R) +
      pi ^ p * ∑ t, cleared t * error t σ
  apply modular_output_barrier E matching embed residue hinjective output terms _ _ d hgap
  · intro σ
    have hidentity := IntegralOutputTransfer.weighted_lift_identity embed pi p q
      (fun t => original t σ) (fun t => replacement t σ) coefficient
      cleared (fun t => error t σ)
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : R)
      (fun t => herr t σ) hclear (hexact σ)
    exact hidentity.symm.trans (hrepresentation σ)
  · intro σ
    have hres := IntegralOutputTransfer.reconstructed_residue residue pi
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : R)
      (∑ t, cleared t * error t σ) p hpi hp
    simpa only [output, map_natCast] using hres

#print axioms exact_count_barrier
#print axioms modular_output_barrier
#print axioms reconstructed_output_barrier

end CertifiedBarrier
