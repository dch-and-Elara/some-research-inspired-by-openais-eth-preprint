import ProductVariance
import GraphCutMoments

/-! Push a uniform vertex law through its actual coordinate labels. The
resulting density gives a second-moment bound for the concrete vertex cuts
in the cubic-expander correlation theorem. -/

namespace EmpiricalCutMoments

open scoped BigOperators

variable {V X I A J : Type*} [Fintype V]

/-- Frequency of label x among uniformly weighted vertices. -/
def empiricalLaw [DecidableEq X] (L : V → X) (x : X) : ℚ :=
  ((Finset.univ.filter fun v => L v = x).card : ℚ) / (Fintype.card V : ℚ)

theorem empiricalLaw_nonneg [DecidableEq X] (L : V → X) (x : X) : 0 ≤ empiricalLaw L x :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Exact change of variables from label frequencies to a uniform average over vertices. -/
theorem empirical_expectation [Fintype X] [DecidableEq X] (L : V → X) (g : X → ℚ) :
    (∑ x, empiricalLaw L x * g x) = (∑ v, g (L v)) / (Fintype.card V : ℚ) := by
  have hterm (x : X) : empiricalLaw L x * g x =
      (((Finset.univ.filter fun v => L v = x).card : ℚ) * g x) / (Fintype.card V : ℚ) := by
    unfold empiricalLaw
    ring
  have hf : (∑ x, ((Finset.univ.filter fun v => L v = x).card : ℚ) * g x) = ∑ v, g (L v) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_fiberwise' Finset.univ L g
  simp only [hterm, div_eq_mul_inv, ← Finset.sum_mul, hf]

theorem sum_empiricalLaw [Nonempty V] [Fintype X] [DecidableEq X] (L : V → X) :
    (∑ x, empiricalLaw L x) = 1 := by
  have hv : (Fintype.card V : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa [hv] using empirical_expectation L (fun _ => 1)

variable [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Fintype J]

/-- The actual set of vertices whose label belongs to a symbol union at one coordinate. -/
def labelCut (L : V → I → A) (owner : J → I) (S : J → Finset A) (j : J) : Finset V :=
  Finset.univ.filter fun v => L v (owner j) ∈ S j

/-- Fraction of all vertices in a specified cut. -/
def cutDensity (T : Finset V) : ℚ := (T.card : ℚ) / (Fintype.card V : ℚ)

omit [Fintype I] [DecidableEq I] [Fintype A] [Fintype J] in
theorem labelCut_bit (L : V → I → A) (owner : J → I) (S : J → Finset A) (j : J) (v : V) :
    GraphCutMoments.cutBit ℚ (labelCut L owner S j) v =
      GraphCutMoments.cutBit ℚ (S j) (L v (owner j)) := by
  simp [GraphCutMoments.cutBit, labelCut]

omit [Fintype J] in
theorem empirical_cut_mean (L : V → I → A) (owner : J → I) (S : J → Finset A) (j : J) :
    (∑ x, empiricalLaw L x * GraphCutMoments.cutBit ℚ (S j) (x (owner j))) =
      cutDensity (labelCut L owner S j) := by
  rw [empirical_expectation]
  simp only [← labelCut_bit L owner S j, cutDensity]
  congr 1
  simp [GraphCutMoments.cutBit]

/-- For actual coordinate cuts on labeled vertices, the empirical density cap
gives the precise vertex signed-moment budget used by GraphCutMoments. -/
theorem vertex_signed_moment [Nonempty V] [Nonempty A]
    (L : V → I → A) (owner : J → I) (S : J → Finset A) (C : ℚ) (hC : 0 ≤ C)
    (hcap : ∀ x, empiricalLaw L x ≤ C * ProductVariance.uniformWeight (I → A)) (eps : J → Bool) :
    (∑ v, (BangCore.signedTotal (fun j u =>
      GraphCutMoments.cutBit ℚ (labelCut L owner S j) u - cutDensity (labelCut L owner S j))
      eps v) ^ 2) / (Fintype.card V : ℚ) ≤
        C * ∑ i, (ProductVariance.coordinateCount owner i : ℚ) ^ 2 := by
  let values (j : J) (a : A) := GraphCutMoments.cutBit ℚ (S j) a
  have hbound (j : J) (a : A) : |values j a| ≤ 1 := by
    dsimp only [values, GraphCutMoments.cutBit]
    split <;> norm_num
  have h := ProductVariance.signed_centered_coordinate_moment (empiricalLaw L) owner values C
    (sum_empiricalLaw L) hC hcap hbound eps
  rw [empirical_expectation] at h
  have hpoint (v : V) :
      BangCore.signedTotal (ProductVariance.centeredCoordinate (empiricalLaw L) owner values) eps (L v) =
        BangCore.signedTotal (fun j u =>
          GraphCutMoments.cutBit ℚ (labelCut L owner S j) u - cutDensity (labelCut L owner S j)) eps v := by
    simp only [BangCore.signedTotal, ProductVariance.centeredCoordinate, values,
      empirical_cut_mean L owner S, labelCut_bit]
  simpa only [hpoint] using h

/-- A direct specialization of the cubic expander theorem to the empirical
product-label setting. The signed vertex moment follows from the density cap,
the owner map, and the numerical choice of H. -/
theorem cubic_expander_label_correlations [Nonempty V] [Nonempty A]
    (E : Finset (V × V)) (hreg : ∀ v, GraphCutMoments.degree E v = 3)
    (L : V → I → A) (owner : J → I) (S : J → Finset A) (C γ η H : ℚ)
    (hC : 0 ≤ C) (hcap : ∀ x, empiricalLaw L x ≤ C * ProductVariance.uniformWeight (I → A))
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hH : 1 ≤ H)
    (hexpand : ∀ T : Finset V,
      γ * (min T.card (Fintype.card V - T.card) : ℕ) ≤ ((GraphCutMoments.boundary E T).card : ℚ))
    (hbalance : ∀ j, η * Fintype.card V ≤
      (min (labelCut L owner S j).card (Fintype.card V - (labelCut L owner S j).card) : ℕ))
    (hscale : C * (∑ i, (ProductVariance.coordinateCount owner i : ℚ) ^ 2) ≤ H ^ 2) :
    ∃ b : E → ℚ, (∀ e, |b e| ≤ 1) ∧ ∀ j,
      γ ^ 2 * η ^ 2 * Fintype.card V / (16 * H) ≤
        |∑ e : E, b e * GraphCutMoments.cutDifference ℚ (labelCut L owner S j) e.1| :=
  GraphCutMoments.cubic_expander_cut_correlations E hreg (labelCut L owner S)
    (fun j => cutDensity (labelCut L owner S j)) γ η H hγ hγ1 hη hη1 hH hexpand hbalance
    (fun eps => (vertex_signed_moment L owner S C hC hcap eps).trans hscale)

#print axioms empiricalLaw_nonneg
#print axioms empirical_expectation
#print axioms sum_empiricalLaw
#print axioms labelCut_bit
#print axioms empirical_cut_mean
#print axioms vertex_signed_moment
#print axioms cubic_expander_label_correlations

end EmpiricalCutMoments
