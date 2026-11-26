import P5A11SharpCommonRange
import P5A11SharpCommonVal
import P5A11SharpCommonPad
import P5A11SharpCommonNative

/-! Paper 5 v7 (A.10), equal precision: extract the ordinary
Smith data of the actual integral confluent Hasse matrix before
reducing coefficients. The same sorted list works for every P.
Singular data are allowed; a zero invariant has valuation infinity. -/
namespace Paper5.CommonJets
open Polynomial Matrix Module
open scoped BigOperators Polynomial Classical

variable {R T : Type*} [CommRing R] [Fintype T] [LinearOrder T]

structure IntegralHasseSmith (π : R) (t a : T→R) (k : T→ℕ) where
  rank : ℕ
  chart : Basis.SmithNormalForm (LinearMap.range (confluentHasseMatrix t a k).mulVecLin)
    (Fin (∑u,k u)) rank
  exp : Fin rank→ℕ
  unit : Fin rank→Rˣ
  factor : ∀ i,chart.a i=(unit i:R)*π^(exp i)
  perm : Equiv.Perm (Fin rank)
  sorted : Monotone (exp∘perm)

noncomputable def IntegralHasseSmith.valuationList {π : R} {t a : T→R} {k : T→ℕ}
    (D : IntegralHasseSmith π t a k) (i : Fin (∑u,k u)) : ENat :=
  paddedValuations (D.exp∘D.perm) i

theorem IntegralHasseSmith.rank_le_size {π : R} {t a : T→R} {k : T→ℕ}
    (D : IntegralHasseSmith π t a k) : D.rank≤∑u,k u := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective D.chart.f D.chart.f.injective

theorem IntegralHasseSmith.valuation_is_infinite {π : R} {t a : T→R} {k : T→ℕ}
    (D : IntegralHasseSmith π t a k) (i : Fin (∑u,k u)) :
    D.valuationList i=⊤ ↔ D.rank ≤ i.val := by
  unfold IntegralHasseSmith.valuationList paddedValuations
  by_cases h : i.val<D.rank
  · rw [dif_pos h]
    exact iff_of_false (ENat.coe_ne_top _) (Nat.not_le.mpr h)
  · rw [dif_neg h]
    exact iff_of_true rfl (Nat.le_of_not_gt h)

theorem IntegralHasseSmith.prime_power_divisibility {π : R} {t a : T→R} {k : T→ℕ}
    (D : IntegralHasseSmith π t a k) (i j : Fin D.rank) (h : i≤j) :
    D.chart.a (D.perm i) ∣ D.chart.a (D.perm j) := by
  rw [D.factor (D.perm i),D.factor (D.perm j),
    (D.unit (D.perm i)).isUnit.mul_left_dvd,(D.unit (D.perm j)).isUnit.dvd_mul_left]
  exact pow_dvd_pow π (D.sorted h)

variable [IsDomain R]

set_option maxHeartbeats 10000000 in
theorem IntegralHasseSmith.uniform_source_image {π : R} {t a : T→R} {k : T→ℕ}
    (D : IntegralHasseSmith π t a k) (hπ : π≠0) (P : ℕ) :
    Nonempty (LinearMap.range (scalarObserve π t a (fun _=>P) k (∑u,k u)) ≃ₗ[R]
      CyclicGrid π (fun (i : Fin (∑u,k u))=>clipped P (D.valuationList i.rev))) := by
  let A := (confluentHasseMatrix t a k).mulVecLin
  obtain ⟨E⟩ := smith_uniform_range π hπ P (LinearMap.range A) D.chart D.exp D.unit D.factor
  rw [reduced_image_from_range] at E
  exact ⟨(sourceImageEquiv π P t a k).symm.trans
    (E.trans (sortPadReverse D.rank_le_size π P D.exp D.perm))⟩

variable [IsLocalRing R] [IsPrincipalIdealRing R]

set_option maxHeartbeats 10000000 in
theorem existence_integral_hasse_smith (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (t a : T→R) (k : T→ℕ) :
    Nonempty (IntegralHasseSmith π t a k) := by
  let F := (confluentHasseMatrix t a k).mulVecLin
  let N := LinearMap.range F
  obtain ⟨r,D⟩ := N.smithNormalForm (Pi.basisFun R (Fin (∑u,k u)))
  obtain ⟨σ,u,hf⟩ := smith_power_factors π hπ hmax N D
  obtain ⟨e,he⟩ := sortedFinPermutation σ
  exact ⟨⟨r,D,σ,u,hf,e,he⟩⟩

set_option maxHeartbeats 10000000 in
theorem a10_common_precision_exact_profile (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (t a : T→R) (k : T→ℕ) :
    ∃ D : IntegralHasseSmith π t a k, Monotone D.valuationList ∧
      ∀ P : ℕ, Monotone (fun (i : Fin (∑u,k u))=>clipped P (D.valuationList i.rev)) ∧
        Nonempty (LinearMap.range (scalarObserve π t a (fun _=>P) k (∑u,k u)) ≃ₗ[R]
          CyclicGrid π (fun (i : Fin (∑u,k u))=>clipped P (D.valuationList i.rev))) := by
  obtain ⟨D⟩ := existence_integral_hasse_smith π hπ hmax t a k
  refine ⟨D,padded_order _ D.sorted,fun P=>⟨?_,D.uniform_source_image hπ P⟩⟩
  exact reversed_clipped_order P _ D.sorted

#print axioms IntegralHasseSmith.rank_le_size
#print axioms IntegralHasseSmith.valuation_is_infinite
#print axioms IntegralHasseSmith.prime_power_divisibility
#print axioms IntegralHasseSmith.uniform_source_image
#print axioms existence_integral_hasse_smith
#print axioms a10_common_precision_exact_profile
end Paper5.CommonJets
