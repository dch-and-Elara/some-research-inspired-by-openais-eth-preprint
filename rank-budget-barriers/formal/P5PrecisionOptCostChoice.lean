import P5PrecisionOptChoices

/-! Exact finite selection with an explicit charged budget. This is an
additional semantic optimization, not the running cost of the printed
acquisition loop. In the payload instance, an omitted node has zero
delivered coefficient bits even if the printed generator computed more. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

def retainedBits (M u p : ℕ) (q : Profile u) : ℕ :=
  ∑ t,q t*(Paper5.P3.rootPrecision u M (Paper5.P3.printedHeight u M) p t.val).toNat

theorem omitted_nodes_no_retained_bits (M u p : ℕ) (q : Profile u) :
    retainedBits M u p q =
      ∑ t∈Paper5.P3.activeNodes q,q t*(Paper5.P3.rootPrecision u M (Paper5.P3.printedHeight u M) p t.val).toNat := by
  unfold retainedBits
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro t _ h
  have hq : q t=0 := by
    by_contra hn
    exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.pos_of_ne_zero hn⟩)
  rw [hq,zero_mul]

noncomputable def exactCostOpt (M u p B : ℕ) (cost : Profile u→ℕ) : ℕ :=
  ((Finset.univ : Finset (OrderChoices M u)).filter (fun x => cost (choiceProfile M u x)≤B)).sup
    (fun x => profileCap M u p (choiceProfile M u x))

theorem finite_cost_optimum_exact {K : Type*} [Field K] [CharZero K]
    (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (M u p B : ℕ) (cost : Profile u→ℕ) {b : ℕ} (hb : 0<b) :
    (∃ q : Profile u, admissibleOrders M u q ∧ cost q≤B ∧ RootCertified O hn2 M u p q b) ↔
      b≤exactCostOpt M u p B cost := by
  let S := (Finset.univ : Finset (OrderChoices M u)).filter
    (fun x => cost (choiceProfile M u x)≤B)
  let f (x : OrderChoices M u) := profileCap M u p (choiceProfile M u x)
  change (∃ q : Profile u, admissibleOrders M u q ∧ cost q≤B ∧ RootCertified O hn2 M u p q b) ↔
      b≤S.sup f
  constructor
  · rintro ⟨q,hq,hw,hcert⟩
    obtain ⟨x,rfl⟩ := every_legal_choice M u q hq
    have hm : x∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩
    have h := (fixed_profile_cap_exact O hn2 M u p (choiceProfile M u x) hb).mp hcert
    exact h.trans (Finset.le_sup (f:=f) hm)
  · intro h
    have he : ∃ x∈S,b≤f x := by
      by_contra hh
      have hm : S.sup f≤b-1 := by
        apply Finset.sup_le
        intro x hx
        have hx' := Nat.lt_of_not_ge (fun (ht : b≤f x) => hh ⟨x,hx,ht⟩)
        omega
      omega
    obtain ⟨x,hx,he⟩ := he
    exact ⟨choiceProfile M u x,every_choice_legal M u x,
      (Finset.mem_filter.mp hx).2,(fixed_profile_cap_exact O hn2 M u p (choiceProfile M u x) hb).mpr he⟩

#print axioms omitted_nodes_no_retained_bits
#print axioms finite_cost_optimum_exact
end Paper5.PrecisionOpt
