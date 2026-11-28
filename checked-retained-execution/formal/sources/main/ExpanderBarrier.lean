import CertifiedBarrier
import CommonMatchingSelection
import EmpiricalCutMoments

/-! A composed finite theorem for the restricted separation interface on
genuine pinned graph CNFs. Its geometric hypotheses describe the actual
graph, label distribution, and coordinate cuts. A common induced matching,
the target's full rank, and the separated-term rank capacities are proved
inside the chain, rather than supplied as hypotheses. -/

namespace ExpanderBarrier

open scoped BigOperators

variable {V I A J T R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype J] [Fintype T]

/-- The concrete geometric and numerical inputs, independent of the output
representation. `owner` may repeat a coordinate; its multiplicities are
counted in `scale`. No common-matching or target-rank claim is a field. -/
structure LabelGeometry (E : Finset (V × V)) (L : V → I → A)
    (owner : J → I) (symbols : J → Finset A) where
  loopless : ∀ v, (v, v) ∉ E
  regular : ∀ v, GraphCutMoments.degree E v = 3
  densityConstant : ℚ
  gamma : ℚ
  eta : ℚ
  H : ℚ
  density_nonneg : 0 ≤ densityConstant
  density : ∀ x, EmpiricalCutMoments.empiricalLaw L x ≤
    densityConstant * ProductVariance.uniformWeight (I → A)
  gamma_pos : 0 < gamma
  gamma_le_one : gamma ≤ 1
  eta_pos : 0 < eta
  eta_le_half : eta ≤ 1 / 2
  H_ge_one : 1 ≤ H
  expansion : ∀ U : Finset V,
    gamma * (min U.card (Fintype.card V - U.card) : ℕ) ≤
      ((GraphCutMoments.boundary E U).card : ℚ)
  balance : ∀ j, eta * Fintype.card V ≤
    (min (EmpiricalCutMoments.labelCut L owner symbols j).card
      (Fintype.card V - (EmpiricalCutMoments.labelCut L owner symbols j).card) : ℕ)
  scale : densityConstant * (∑ i, (ProductVariance.coordinateCount owner i : ℚ) ^ 2) ≤ H ^ 2

variable {E : Finset (V × V)} {L : V → I → A}
variable {owner : J → I} {symbols : J → Finset A}

/-- Half the uniform lower bound for the expected oriented cut statistic.
The crude cubic block bound is 36; sharp constants are not asserted here. -/
def margin (G : LabelGeometry E L owner symbols) : ℚ :=
  CommonMatchingSelection.rate 36 * G.gamma ^ 2 * G.eta ^ 2 * Fintype.card V / (32 * G.H)

omit [Nonempty A] in
theorem margin_pos (G : LabelGeometry E L owner symbols) : 0 < margin G := by
  have hg := G.gamma_pos
  have he := G.eta_pos
  have hH : 0 < G.H := zero_lt_one.trans_le G.H_ge_one
  have hN : 0 < (Fintype.card V : ℚ) := by exact_mod_cast Fintype.card_pos (α := V)
  have hr := CommonMatchingSelection.rate_pos 36
  unfold margin
  positivity

/-- The second moment and union-bound condition for the actual finite menu.
Its cardinality is the number of available cuts, not the number of terms. -/
def SelectionBudget (G : LabelGeometry E L owner symbols) : Prop :=
  (Fintype.card J : ℚ) * ((4 * (E.card : ℚ) * (36 * 36 : ℕ)) / margin G ^ 2) < 1

/-- The finite label, expansion, and concentration assumptions produce one
genuine induced matching which simultaneously unbalances every menu cut. -/
theorem common_matching (G : LabelGeometry E L owner symbols)
    (d : ℕ) (hd : (d : ℚ) ≤ margin G) (hbudget : SelectionBudget G) :
    ∃ mark orientation : E → Bool, ∀ j,
      d ≤ SeparatedRank.endpointImbalance
        (MatchingThinning.matching E G.loopless mark orientation).endpoint
        (EmpiricalCutMoments.labelCut L owner symbols j) := by
  classical
  obtain ⟨b, hb, hcorr⟩ := EmpiricalCutMoments.cubic_expander_label_correlations
    E G.regular L owner symbols G.densityConstant G.gamma G.eta G.H
    G.density_nonneg G.density G.gamma_pos G.gamma_le_one G.eta_pos G.eta_le_half
    G.H_ge_one G.expansion G.balance G.scale
  apply CommonMatchingSelection.select_degree E G.loopless 3
    (fun v => (G.regular v).le) (EmpiricalCutMoments.labelCut L owner symbols)
    b hb (margin G) d (margin_pos G) hd
  · intro j
    change 2 * margin G ≤ CommonMatchingSelection.rate 36 * _
    calc
      _ = CommonMatchingSelection.rate 36 *
          (G.gamma ^ 2 * G.eta ^ 2 * Fintype.card V / (16 * G.H)) := by
        unfold margin
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr j) (CommonMatchingSelection.rate_pos 36).le
  · exact hbudget

variable [CommRing R] [CommRing S] [Nontrivial S] [Field K]

/-- An exact count representation on the real CNF family needs at least
2^d separated terms. Each term selects one cut from the actual finite menu. -/
theorem exact_count_barrier (G : LabelGeometry E L owner symbols)
    (d : ℕ) (hd : (d : ℚ) ≤ margin G) (hbudget : SelectionBudget G)
    (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ t, (terms t).side = EmpiricalCutMoments.labelCut L owner symbols (assigned t))
    (hrepresentation : ∀ σ, (PinnedCNF.modelCount (PinnedCNF.formula E σ) : K) =
      ∑ t, (terms t).value σ) :
    2 ^ d ≤ Fintype.card T := by
  classical
  obtain ⟨mark, orientation, hgap⟩ := common_matching G d hd hbudget
  apply CertifiedBarrier.exact_count_barrier E
    (MatchingThinning.matching E G.loopless mark orientation) terms hrepresentation d
  intro t
  rw [hside t]
  exact hgap (assigned t)

/-- Only the final reconstructed output must be integral and correct in the
residue ring. Individual field-valued summands can be signed or fractional. -/
theorem modular_output_barrier (G : LabelGeometry E L owner symbols)
    (d : ℕ) (hd : (d : ℚ) ≤ margin G) (hbudget : SelectionBudget G)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R) (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ t, (terms t).side = EmpiricalCutMoments.labelCut L owner symbols (assigned t))
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    2 ^ d ≤ Fintype.card T := by
  classical
  obtain ⟨mark, orientation, hgap⟩ := common_matching G d hd hbudget
  apply CertifiedBarrier.modular_output_barrier E
    (MatchingThinning.matching E G.loopless mark orientation) embed residue hinjective
    output terms hrepresentation hcorrect d
  intro t
  rw [hside t]
  exact hgap (assigned t)

/-- The finite precision/clearing identity is connected all the way to the
same geometric bound, without assuming a rank bound for the integral output. -/
theorem reconstructed_output_barrier {U : Type*} [Fintype U]
    (G : LabelGeometry E L owner symbols)
    (d : ℕ) (hd : (d : ℚ) ≤ margin G) (hbudget : SelectionBudget G)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (pi : R) (p : ℕ) (q : U → ℕ) (coefficient : U → K) (cleared : U → R)
    (original replacement error : U → (V → Bool) → R)
    (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ t, (terms t).side = EmpiricalCutMoments.labelCut L owner symbols (assigned t))
    (herr : ∀ u σ, replacement u σ = original u σ + pi ^ q u * error u σ)
    (hclear : ∀ u, coefficient u * embed (pi ^ q u) = embed (pi ^ p * cleared u))
    (hexact : ∀ σ, (∑ u, coefficient u * embed (original u σ)) =
      embed (PinnedCNF.modelCount (PinnedCNF.formula E σ) : R))
    (hrepresentation : ∀ σ, (∑ u, coefficient u * embed (replacement u σ)) =
      ∑ t, (terms t).value σ)
    (hpi : residue pi = 0) (hp : 0 < p) :
    2 ^ d ≤ Fintype.card T := by
  classical
  obtain ⟨mark, orientation, hgap⟩ := common_matching G d hd hbudget
  apply CertifiedBarrier.reconstructed_output_barrier E
    (MatchingThinning.matching E G.loopless mark orientation) embed residue hinjective
    pi p q coefficient cleared original replacement error terms herr hclear hexact
    hrepresentation hpi hp d
  intro t
  rw [hside t]
  exact hgap (assigned t)

#print axioms margin_pos
#print axioms common_matching
#print axioms exact_count_barrier
#print axioms modular_output_barrier
#print axioms reconstructed_output_barrier

end ExpanderBarrier
