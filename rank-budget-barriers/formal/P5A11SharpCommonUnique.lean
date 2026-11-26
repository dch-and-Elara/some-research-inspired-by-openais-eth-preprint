import P5A10Full

/-! A sorted list of cyclic lengths is intrinsic to the finite
observation image, not just to the chosen Smith chart. Truncated
power-layer length profiles detect all multiplicities and zeros. -/
namespace Paper5.CommonJets
open scoped BigOperators Classical
open Module

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

noncomputable def powerImageCongr (π : R) (k : ℕ) (E : M ≃ₗ[R] N) :
    PowerImage π k M ≃ₗ[R] PowerImage π k N :=
  LinearEquiv.ofBijective (powImageMap π k E.toLinearMap)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact E.injective (congrArg Subtype.val h),
      powImageMap_surjective π k E.toLinearMap E.surjective⟩

theorem positive_tail_step {n : ℕ} (q : Fin n→ℕ) (h : ℕ) :
    (∑ i, (q i-h)) = (∑ i,(q i-(h+1))) +
      (Finset.univ.filter (fun i=>h<q i)).card := by
  have hp (i : Fin n) : q i-h=(q i-(h+1))+(if h<q i then 1 else 0) := by
    by_cases h' : h<q i <;> simp [h'] <;> omega
  calc
    _ = ∑ i, ((q i-(h+1))+(if h<q i then 1 else 0)) :=
      Finset.sum_congr rfl (fun i _=>hp i)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have hc : (∑ i : Fin n, (if h<q i then (1:ℕ) else 0)) =
          ∑ _i ∈ Finset.univ.filter (fun i=>h<q i), (1:ℕ) := by
        rw [Finset.sum_filter]
      rw [hc]
      simp

theorem count_sup_preserves_order {n : ℕ} (q r : Fin n→ℕ)
    (hq : Monotone q) (hr : Monotone r)
    (h : ∀ k, (Finset.univ.filter (fun i=>k<q i)).card =
      (Finset.univ.filter (fun i=>k<r i)).card) (i : Fin n) :
    ¬ q i<r i := by
  intro hi
  let I := Finset.univ.filter (fun j : Fin n=>i≤j)
  let J := Finset.univ.filter (fun j : Fin n=>i<j)
  have hI (j : Fin n) : j∈I ↔ i≤j := by simp [I]
  have hJ (j : Fin n) : j∈J ↔ i<j := by simp [J]
  have ha : Finset.univ.filter (fun j=>q i<q j) ⊆ J := by
    intro j hj
    apply (hJ j).2
    apply lt_of_not_ge
    intro hji
    exact (not_lt_of_ge (hq hji)) (Finset.mem_filter.mp hj).2
  have hb : I ⊆ Finset.univ.filter (fun j=>q i<r j) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.trans_le (hr ((hI j).mp hj))⟩
  have hc : J ⊂ I := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun j hj=>(hI j).2 ((hJ j).1 hj).le,?_⟩
    intro he
    have hp : i∈J := by rw [he]; exact (hI i).2 le_rfl
    exact (lt_irrefl i) ((hJ i).mp hp)
  exact (lt_irrefl _)
    (((Finset.card_le_card ha).trans_lt (Finset.card_lt_card hc)).trans_le
      ((Finset.card_le_card hb).trans_eq (h (q i)).symm))

variable [IsDomain R]

theorem sorted_cyclic_profile_unique {n : ℕ} (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (q r : Fin n→ℕ)
    (hq : Monotone q) (hr : Monotone r) (E : CyclicGrid π q ≃ₗ[R] CyclicGrid π r) :
    q=r := by
  have hs (k : ℕ) : (∑i,(q i-k))=(∑i,(r i-k)) := by
    have he := (powerImageCyclicGrid_length π hπ hmax q k).symm.trans
      ((powerImageCongr π k E).length_eq.trans (powerImageCyclicGrid_length π hπ hmax r k))
    simpa only [ENat.toNat_coe] using congrArg ENat.toNat he
  have hc (k : ℕ) : (Finset.univ.filter (fun i=>k<q i)).card =
      (Finset.univ.filter (fun i=>k<r i)).card := by
    have he := hs k
    rw [positive_tail_step q k,positive_tail_step r k,hs (k+1)] at he
    exact Nat.add_left_cancel he
  funext i
  exact le_antisymm (le_of_not_gt (count_sup_preserves_order r q hr hq (fun k=>(hc k).symm) i))
    (le_of_not_gt (count_sup_preserves_order q r hq hr hc i))

#print axioms powerImageCongr
#print axioms positive_tail_step
#print axioms count_sup_preserves_order
#print axioms sorted_cyclic_profile_unique
end Paper5.CommonJets
