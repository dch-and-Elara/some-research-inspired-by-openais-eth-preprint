import J6ActiveAllocation

/-! Collect the exact affine expansion by mode multiplicities. The
profile carrier is finite and imposes no artificial distinct-mode condition. -/
namespace J6ActiveProfile
open scoped BigOperators Classical
variable {I M R : Type*} [Fintype I] [Fintype M] [CommRing R]
open J6ActiveAllocation

noncomputable def count (x : I→Option M) (m : M) : ℕ :=
  (Finset.univ.filter (fun i => x i = some m)).card

noncomputable def profile (x : I→Option M) (m : M) : Fin (Fintype.card I+1) :=
  ⟨count x m, Nat.lt_succ_of_le (Finset.card_filter_le _ _)⟩

def profileWeight (w : M→ℕ) (r : M→Fin (Fintype.card I+1)) : ℕ :=
  ∑ m, (r m).val*w m

theorem weight_eq (w : M→ℕ) (x : I→Option M) :
    total w x = profileWeight w (profile x) := by
  classical
  unfold total profileWeight
  have h (i : I) : cost w (x i) =
      ∑ m : M, if x i = some m then w m else 0 := by
    cases e : x i with
    | none => simp [cost]
    | some m => simp [cost]
  simp only [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_filter]
  simp [profile,count]

theorem collect_by_profile (w : M→ℕ) (f : I→Option M→R)
    (p : ℕ) (hR : (2:R)^p=0) :
    (∏ i, ∑ v : Option M, scaled w f i v) =
      ∑ b : M→Fin (Fintype.card I+1),
        if profileWeight w b<p then
          ∑ x : I→Option M,
            if profile x=b then ∏ i, scaled w f i (x i) else 0
        else 0 := by
  rw [truncated_expansion w f p hR,Finset.sum_filter]
  symm
  trans ∑ b : M→Fin (Fintype.card I+1), ∑ x : I→Option M,
    if profileWeight w b<p ∧ profile x=b then ∏ i, scaled w f i (x i) else 0
  · apply Finset.sum_congr rfl
    intro b _
    by_cases hb : profileWeight w b<p <;> simp [hb]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single_of_mem (profile x) (Finset.mem_univ _)]
  · simp [← weight_eq]
  · intro b _ hb
    simp [Ne.symm hb]

#print axioms weight_eq
#print axioms collect_by_profile
end J6ActiveProfile