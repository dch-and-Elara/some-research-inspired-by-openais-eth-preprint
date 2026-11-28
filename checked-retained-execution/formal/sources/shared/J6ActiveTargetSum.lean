import J6TargetProfile

/-! Discarding a target-incorrect allocation is valid before counting its
multiplicity: the off-block coefficient is actually zero. -/
namespace J6ActiveTargetSum
open scoped BigOperators Classical
open J6ActiveAllocation J6ActiveProfile J6TargetProfile
variable {R I M K : Type*} [CommRing R] [Fintype I] [Fintype M]

def Legal (block : I→K) (target : M→K) (x : I→Option M) : Prop :=
  ∀ i m, x i = some m → block i = target m

omit [Fintype M] in
theorem incorrect_erase (w : M→ℕ) (f : I→Option M→R) (block : I→K)
    (target : M→K) (hzero : ∀ i m, block i≠target m → f i (some m)=0)
    (x : I→Option M) (hx : ¬ Legal block target x) :
    (∏ i, scaled w f i (x i)) = 0 := by
  unfold Legal at hx
  push_neg at hx
  obtain ⟨i,m,hm,hn⟩ := hx
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [hm,scaled,hzero i m hn,mul_zero]

theorem by_legal_target_profile (w : M→ℕ) (f : I→Option M→R)
    (p : ℕ) (hR : (2:R)^p=0) (block : I→K) (target : M→K)
    (hzero : ∀ i m, block i≠target m → f i (some m)=0) :
    (∏ i, ∑ v : Option M, scaled w f i v) =
      ∑ b : M→Fin (Fintype.card I+1),
        if profileWeight w b<p then
          ∑ x : I→Option M,
            if Legal block target x ∧
              (∀ m, count (fun j : {i : I // block i=target m} => x j.val) m = (b m).val)
            then ∏ i, scaled w f i (x i) else 0
        else 0 := by
  rw [collect_by_profile w f p hR]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : profileWeight w b<p
  · rw [if_pos hb,if_pos hb]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : Legal block target x
    · have hloc := profile_is_local x block target hx b
      by_cases h : profile x = b
      · simp [hx,h,hloc.mp h]
      · have hn := fun h' => h (hloc.mpr h')
        rw [if_neg h,if_neg (fun hh => hn hh.2)]
    · have he := incorrect_erase w f block target hzero x hx
      simp [hx,he]
  · simp [hb]

#print axioms incorrect_erase
#print axioms by_legal_target_profile
end J6ActiveTargetSum