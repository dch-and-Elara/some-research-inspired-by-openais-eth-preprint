import P5A11SharpCommonFinal
import P5A11SharpCommonUnique

/-! The q_i in A.10 are the actual sorted profile, independent of how
an earlier cyclic decomposition is selected. The integral valuation
profile is also independent of Smith-chart choices on the source. -/
namespace Paper5.CommonJets
open scoped BigOperators Polynomial Classical
open Module

theorem clip_separates (s t : ENat) (h : ∀ P,clipped P s=clipped P t) : s=t := by
  by_cases hs : s=⊤
  · by_cases ht : t=⊤
    · exact hs.trans ht.symm
    · obtain ⟨n,rfl⟩ := ENat.ne_top_iff_exists.mp ht
      have f := h (n+1)
      rw [hs,clipped_top,clipped_coe] at f
      omega
  · obtain ⟨m,rfl⟩ := ENat.ne_top_iff_exists.mp hs
    by_cases ht : t=⊤
    · have f := h (m+1)
      rw [ht,clipped_top,clipped_coe] at f
      omega
    · obtain ⟨n,rfl⟩ := ENat.ne_top_iff_exists.mp ht
      have f := h (m+n+1)
      rw [clipped_coe,clipped_coe] at f
      have hmn : m=n := by omega
      simp [hmn]

variable {R T : Type*} [CommRing R] [IsDomain R] [Fintype T] [LinearOrder T]

theorem printed_sorted_q_is_reversed_smith {π : R} {t a : T→R} {k : T→ℕ}
    (D : IntegralHasseSmith π t a k) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (P : ℕ) (q : Fin (∑u,k u)→ℕ) (hq : Monotone q)
    (E : LinearMap.range (scalarObserve π t a (fun _=>P) k (∑u,k u)) ≃ₗ[R] CyclicGrid π q) :
    q=fun (i : Fin (∑u,k u))=>clipped P (D.valuationList i.rev) := by
  obtain ⟨F⟩ := D.uniform_source_image hπ P
  exact sorted_cyclic_profile_unique π hπ hmax _ _ hq
    (reversed_clipped_order P _ D.sorted) (E.symm.trans F)

theorem integral_hasse_valuations_unique {π : R} {t a : T→R} {k : T→ℕ}
    (D E : IntegralHasseSmith π t a k) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) :
    D.valuationList=E.valuationList := by
  funext i
  apply clip_separates
  intro P
  obtain ⟨F⟩ := D.uniform_source_image hπ P
  have he := printed_sorted_q_is_reversed_smith E hπ hmax P _
    (reversed_clipped_order P _ D.sorted) F
  have h := congrFun he i.rev
  simpa only [Fin.rev_rev] using h

theorem uniform_native_image_exact_length {π : R} {t a : T→R} {k : T→ℕ}
    (D : IntegralHasseSmith π t a k) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (P : ℕ) :
    Module.length R (LinearMap.range (scalarObserve π t a (fun _=>P) k (∑u,k u))) =
      ((∑ i : Fin (∑u,k u),clipped P (D.valuationList i.rev):ℕ):ENat) := by
  obtain ⟨F⟩ := D.uniform_source_image hπ P
  rw [F.length_eq,cyclicGrid_length π hπ hmax]

#print axioms clip_separates
#print axioms printed_sorted_q_is_reversed_smith
#print axioms integral_hasse_valuations_unique
#print axioms uniform_native_image_exact_length
end Paper5.CommonJets
