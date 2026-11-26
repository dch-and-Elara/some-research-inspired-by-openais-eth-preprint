import J6BlockFactor

namespace J6FixedProfile
open scoped BigOperators Classical
open J6ActiveAllocation J6ActiveProfile J6TargetProfile J6ActiveTargetSum J6BlockFactor
variable {R I M K : Type*} [CommRing R] [Fintype I] [Fintype M] [Fintype K]

noncomputable def test (block : I → K) (target : M → K)
    (b : M → Fin (Fintype.card I + 1))
    (k : K) (y : rows block k → Option M) : Prop :=
  (∀ i m, y i = some m → k = target m) ∧
  (∀ m : modes target k, count y m.val = (b m.val).val)

omit [CommRing R] [Fintype K] [Fintype M] in
theorem all_tests (block : I → K) (target : M → K)
    (b : M → Fin (Fintype.card I + 1)) (x : I → Option M) :
    (∀ k, test block target b k (allocationEquiv block x k)) ↔
      Legal block target x ∧
        (∀ m, count (fun j : {i : I // block i = target m} => x j.val) m = (b m).val) := by
  classical
  constructor
  · intro h
    refine ⟨(legal_iff_local block target x).mpr (fun k => (h k).1), ?_⟩
    intro m
    have hm := (h (target m)).2 ⟨m, rfl⟩
    exact hm
  · rintro ⟨hl, hc⟩ k
    refine ⟨(legal_iff_local block target x).mp hl k, ?_⟩
    rintro ⟨m, hm⟩
    change target m = k at hm
    subst k
    exact hc m

noncomputable def targetCoeff (w : M → ℕ) (f : I → Option M → R)
    (block : I → K) (target : M → K) (b : M → Fin (Fintype.card I+1)) (k : K) : R :=
  ∑ y : rows block k → Option M,
    if test block target b k y
    then ∏ i : rows block k, scaled w f i.val (y i) else 0

/-- Each source moment occurs once, not once per chosen row or target.
  The input rows may already depend on shared bit assignments. -/
theorem sum_modes_blocked (w : M → ℕ) (f : I → Option M → R)
    (p : ℕ) (hR : (2:R)^p=0) (block : I → K) (target : M → K)
    (hzero : ∀ i m, block i ≠ target m → f i (some m)=0) :
      (∏ i, ∑ v : Option M, scaled w f i v) =
      ∑ b : M → Fin (Fintype.card I+1),
        if profileWeight w b < p then
          ∏ k, targetCoeff w f block target b k
        else 0 := by
  classical
  rw [by_legal_target_profile w f p hR block target hzero]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : profileWeight w b < p
  · rw [if_pos hb, if_pos hb]
    simp only [← all_tests block target b]
    simpa only [targetCoeff, Finset.prod_const_one, one_mul] using
      (sum_with_block_test block (test block target b) (scaled w f) (fun _ _ => 1))
  · simp only [if_neg hb]

#print axioms all_tests
#print axioms sum_modes_blocked
end J6FixedProfile
