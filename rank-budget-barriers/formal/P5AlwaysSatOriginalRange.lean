import P5AlwaysSatOriginalCount
import Mathlib.Data.Nat.Log

/-! Reachable exact counts of the original switch CNF. The count of any
one weight lies in its own two-element dyadic interval; every weight on
T is achieved without a promise on the edge coverage bit. -/
namespace Paper5.AlwaysSatOriginal
variable {V : Type*}

theorem count_dyadic_interval [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    2^(1+(activeBonus T s).card)≤PinnedCNF.modelCount (formula E T s) ∧
    PinnedCNF.modelCount (formula E T s)<2^(2+(activeBonus T s).card) := by
  rw [original_model_count]
  have hP : 2≤(2:ℕ)^(1+(activeBonus T s).card) := by
    change (2:ℕ)^1≤(2:ℕ)^(1+(activeBonus T s).card)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hC := cover_bit_le_one E s
  refine ⟨Nat.le_add_right _ _,?_⟩
  rw [show 2+(activeBonus T s).card=(1+(activeBonus T s).card)+1 by omega,pow_succ']
  omega

/-- The binary length is exact, including the y=1 completion when present. -/
theorem original_binary_length [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    Nat.log 2 (PinnedCNF.modelCount (formula E T s))+1=(activeBonus T s).card+2 := by
  have hh := count_dyadic_interval E T s
  have hp : 0<PinnedCNF.modelCount (formula E T s) :=
    (pow_pos (by decide : 0<(2:ℕ)) _).trans_le hh.1
  have hl := (Nat.le_log_iff_pow_le (by decide : 1<(2:ℕ)) hp.ne').mpr hh.1
  have hu := (Nat.log_lt_iff_lt_pow (by decide : 1<(2:ℕ)) hp.ne').mpr hh.2
  omega

theorem every_weight_reached (T : Finset V) {j : ℕ} (hj : j≤T.card) :
    ∃ s : V→Bool,(activeBonus T s).card=j := by
  classical
  obtain ⟨U,hUT,hU⟩ := Finset.exists_subset_card_eq hj
  refine ⟨maskOf U,?_⟩
  have hEq : T.filter (fun v=>maskOf U v=true)=U := by
    ext v
    simp only [Finset.mem_filter,maskOf,decide_eq_true_eq]
    exact ⟨And.right,fun hv=>⟨hUT hv,hv⟩⟩
  rw [active_bonus_card,hEq,hU]

noncomputable def signAtWeight (T : Finset V) (j : Fin (T.card+1)) : V→Bool :=
  Classical.choose (every_weight_reached T (Nat.le_of_lt_succ j.isLt))

theorem weight_of_signAtWeight (T : Finset V) (j : Fin (T.card+1)) :
    (activeBonus T (signAtWeight T j)).card=j.val :=
  Classical.choose_spec (every_weight_reached T (Nat.le_of_lt_succ j.isLt))

theorem two_weights_distinct_counts [Fintype V] (E : Finset (V×V)) (T : Finset V)
    (s s' : V→Bool) (h : (activeBonus T s).card≠(activeBonus T s').card) :
    PinnedCNF.modelCount (formula E T s)≠PinnedCNF.modelCount (formula E T s') := by
  intro he
  apply h
  have hl := original_binary_length E T s
  have hr := original_binary_length E T s'
  rw [he] at hl
  omega

noncomputable def actualCounts [Fintype V] (E : Finset (V×V)) (T : Finset V) : Finset ℕ := by
  classical
  exact (Finset.univ : Finset (V→Bool)).image fun s=>PinnedCNF.modelCount (formula E T s)

theorem at_least_K_plus_one_counts [Fintype V] (E : Finset (V×V)) (T : Finset V) :
    T.card+1≤(actualCounts E T).card := by
  classical
  let f (j : Fin (T.card+1)) := PinnedCNF.modelCount (formula E T (signAtWeight T j))
  have hi : Function.Injective f := by
    intro i j he
    apply Fin.ext
    by_contra hn
    apply (two_weights_distinct_counts E T (signAtWeight T i) (signAtWeight T j) ?_) he
    rw [weight_of_signAtWeight,weight_of_signAtWeight]
    exact hn
  have hf : Set.MapsTo f
      ((Finset.univ : Finset (Fin (T.card+1))) : Set _) (actualCounts E T : Set _) := by
    intro j _
    exact Finset.mem_image.mpr ⟨signAtWeight T j,Finset.mem_univ _,rfl⟩
  simpa using (Finset.card_le_card_of_injOn f hf hi.injOn)

theorem true_pin_binary_length [Fintype V] (E : Finset (V×V)) (T : Finset V) :
    Nat.log 2 (PinnedCNF.modelCount (formula E T (fun _=>true)))+1=T.card+2 := by
  rw [original_binary_length,active_bonus_card]
  simp

theorem quarter_family_many_counts [Fintype V] (E : Finset (V×V)) :
    ∃ T : Finset V,
      T.card=Fintype.card V/4 ∧
      Fintype.card V/4+1≤(actualCounts E T).card ∧
      (∀ s : V→Bool,(formula E T s).Sat (assignment T s false false (fun _=>false))) ∧
      Nat.log 2 (PinnedCNF.modelCount (formula E T (fun _=>true)))+1=Fintype.card V/4+2 := by
  classical
  have ht : Fintype.card V/4≤(Finset.univ : Finset V).card := by simp [Nat.div_le_self]
  obtain ⟨T,_,hT⟩ := Finset.exists_subset_card_eq ht
  refine ⟨T,hT,?_,all_signs_sat E T,?_⟩
  · simpa [hT] using at_least_K_plus_one_counts E T
  · rw [true_pin_binary_length,hT]

/-- The literal easy graph/bonus-weight evaluation; no claim about the
cost of the original interpolation evaluator follows. -/
def scanCount (E : Finset (V×V)) (T : Finset V) (s : V→Bool) : ℕ :=
  2^(1+(T.filter fun v=>s v=true).card)+
    (if (E.filter fun e=>s e.1=false ∧ s e.2=false).Nonempty then 0 else 1)

theorem scan_count_exact [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    scanCount E T s=PinnedCNF.modelCount (formula E T s) := by
  classical
  have hE : ¬(E.filter fun e=>s e.1=false ∧ s e.2=false).Nonempty ↔ PinnedCNF.AllEdges E s := by
    constructor
    · intro h e he
      cases hL : s e.1
      · cases hR : s e.2
        · exact (h ⟨e,Finset.mem_filter.mpr ⟨he,hL,hR⟩⟩).elim
        · exact Or.inr rfl
      · exact Or.inl rfl
    · intro h hA
      obtain ⟨e,hm⟩ := hA
      obtain ⟨he,hL,hR⟩ := Finset.mem_filter.mp hm
      simpa [hL,hR] using h e he
  rw [scanCount,original_model_count,active_bonus_card]
  by_cases hc : PinnedCNF.AllEdges E s
  · simp [coverBit,hc,hE.mpr hc]
  · have hh : (E.filter fun e=>s e.1=false ∧ s e.2=false).Nonempty := by
      by_contra hn
      exact hc (hE.mp hn)
    simp [coverBit,hc,hh]

#print axioms count_dyadic_interval
#print axioms original_binary_length
#print axioms every_weight_reached
#print axioms weight_of_signAtWeight
#print axioms two_weights_distinct_counts
#print axioms at_least_K_plus_one_counts
#print axioms true_pin_binary_length
#print axioms quarter_family_many_counts
#print axioms scan_count_exact
end Paper5.AlwaysSatOriginal