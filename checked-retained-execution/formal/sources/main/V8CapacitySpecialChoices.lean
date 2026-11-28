import V8CapacitySpecialSignatures

/-! J2 at the exact ordinary coefficient level. The occurrence
multinomial is defined by its standard histogram-count interpretation,
so reduction from natural coefficients to O includes equal-char zeros. -/
namespace V8CapacitySpecialChoices
open scoped Polynomial Classical BigOperators
open V8CapacitySymbolic V8CapacitySpecialSignatures

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {H O : Type*} [Fintype H] [CommRing O] {k : ℕ}

def zeroWeight (d : Digits H k →₀ ℕ) : ℕ :=
  ∑ e : Digits H k, if e.2.val=0 then d e else 0

theorem choice_zeroweight (a : H → ℕ) (c : Occ a → Fin k) :
    zeroWeight (choiceExp Finset.univ c)=choiceZeros Finset.univ c := by
  unfold zeroWeight choiceExp choiceZeros
  simp only [Finsupp.finset_sum_apply]
  have h :
      (∑ e : Digits H k, if e.2.val=0 then
        ∑ u : Occ a, (Finsupp.single (u.1,c u) (1:ℕ)) e else 0) =
      ∑ e : Digits H k, ∑ u : Occ a, if e.2.val=0 then
        (Finsupp.single (u.1,c u) (1:ℕ)) e else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp
  rw [h,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single_of_mem (u.1,c u) (Finset.mem_univ _)]
  · rw [Finsupp.single_eq_same]
  · intro x _ hx
    rw [Finsupp.single_eq_of_ne hx]
    split_ifs <;> rfl

def rowHist {a : ℕ} (f : Fin a → Fin k) (r : Fin k) : ℕ :=
  ∑ t : Fin a, if f t=r then 1 else 0

theorem choice_rowHist (a : H → ℕ) (c : Occ a → Fin k) (i : H) (r : Fin k) :
    choiceExp Finset.univ c (i,r)=rowHist (fun t => c ⟨i,t⟩) r := by
  unfold choiceExp rowHist
  simp only [Finsupp.finset_sum_apply]
  rw [Fintype.sum_sigma,Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · apply Finset.sum_congr rfl
    intro t _
    rw [Finsupp.single_apply]
    simp
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro t _
    apply Finsupp.single_eq_of_ne
    intro h
    exact hj (congrArg Prod.fst h).symm

abbrev choiceWords (a : H → ℕ) (d : Digits H k →₀ ℕ) :=
  {c : Occ a → Fin k // choiceExp Finset.univ c=d}

abbrev rowWords (n : ℕ) (b : Fin k → ℕ) :=
  {f : Fin n → Fin k // ∀ r : Fin k, rowHist f r=b r}

def choice_product (a : H → ℕ) (d : Digits H k →₀ ℕ) :
    choiceWords a d ≃ ((i : H) → rowWords (a i) (fun r => d (i,r))) where
  toFun c i := ⟨fun t => c.val ⟨i,t⟩,fun r => by
    rw [← choice_rowHist a c.val i r,c.property]⟩
  invFun f := ⟨fun t => (f t.fst).val t.snd,by
    ext e
    obtain ⟨i,r⟩ := e
    rw [choice_rowHist]
    exact (f i).property r⟩
  left_inv c := by
    apply Subtype.ext
    funext u
    cases u
    rfl
  right_inv f := by
    funext i
    apply Subtype.ext
    rfl

/-- The usual multinomial coefficient: the number of words with these
letter multiplicities, equivalently the number of labeled allocations.
It is zero if they do not sum to n. -/
def wordMultinomial (n : ℕ) (b : Fin k → ℕ) : ℕ :=
  Fintype.card (rowWords n b)

theorem choice_count (a : H → ℕ) (d : Digits H k →₀ ℕ) :
    Fintype.card (choiceWords a d)=∏ i : H, wordMultinomial (a i) (fun r => d (i,r)) := by
  rw [Fintype.card_congr (choice_product a d),Fintype.card_pi]
  rfl

/-- Exact J2 coefficient formula with the multinomial in its
histogram-count definition. There are no monomial collisions between
different signatures; any cancellation occurs only after the natural
coefficients are mapped to the actual base ring. -/
theorem coefficient_multinomial_count (π : O) (hk : 0<k) (a : H → ℕ)
    (j : ℕ) (d : Digits H k →₀ ℕ) :
    (feature π k a j).coeff d =
      if zWeight d=j then π^zeroWeight d *
        ((∏ i : H, wordMultinomial (a i) (fun r => d (i,r))):ℕ) else 0 := by
  rw [exact_choice_coeff π hk a j d]
  by_cases h : zWeight d=j
  · rw [if_pos h,← choice_count]
    have hex (c : Occ a → Fin k) :
        (if j=choiceWeight Finset.univ c then
          if choiceExp Finset.univ c=d then π^choiceZeros Finset.univ c else 0 else 0)=
          if choiceExp Finset.univ c=d then π^zeroWeight d else 0 := by
      by_cases he : choiceExp Finset.univ c=d
      · have hW : j=choiceWeight Finset.univ c :=
          h.symm.trans (he ▸ choice_zweight a c)
        rw [if_pos hW,if_pos he,if_pos he,← choice_zeroweight a c,he]
      · rw [if_neg he]
        split_ifs <;> rfl
    simp_rw [hex,← Finset.sum_filter]
    let s := Finset.univ.filter (fun c : Occ a → Fin k => choiceExp Finset.univ c=d)
    have hcard : s.card=Fintype.card (choiceWords a d) := by
      exact (Fintype.card_of_subtype s (p:=fun c => choiceExp Finset.univ c=d)
        (fun c => by simp [s])).symm
    rw [Finset.sum_const,hcard,nsmul_eq_mul,mul_comm]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with hW he
    · exact False.elim (h (he ▸ (choice_zweight a c).trans hW.symm))
    · rfl
    · rfl

#print axioms choice_zeroweight
#print axioms choice_rowHist
#print axioms choice_product
#print axioms choice_count
#print axioms coefficient_multinomial_count
end
end V8CapacitySpecialChoices

