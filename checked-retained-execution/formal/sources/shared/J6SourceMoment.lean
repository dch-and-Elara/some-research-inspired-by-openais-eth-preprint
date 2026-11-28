import J6FixedProfile

namespace J6SourceMoment
open scoped BigOperators Classical
open J6ActiveAllocation J6ActiveProfile J6ActiveTargetSum J6BlockFactor J6FixedProfile
variable {R I M K : Type*} [CommRing R] [Fintype I] [Fintype M] [Fintype K]

def insert (f : I → Option M → R) (L : M → R) (i : I) (v : Option M) : R :=
  f i v * v.elim' 1 L

theorem moment_of_choices (x : I → Option M) (L : M → R) :
    (∏ i, (x i).elim' 1 L) = ∏ m, L m ^ count x m := by
  classical
  have h (i : I) : (x i).elim' 1 L = ∏ m : M, if x i = some m then L m else 1 := by
    cases e : x i with
    | none => simp
    | some m => simp
  simp only [h]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro m _
  rw [← Finset.prod_filter]
  simp [count]

theorem sum_modes_with_moments (w : M → ℕ) (f : I → Option M → R)
    (L : M → R) (p : ℕ) (hR : (2:R)^p=0)
    (block : I → K) (target : M → K)
    (hzero : ∀ i m, block i ≠ target m → f i (some m)=0) :
    (∏ i, ∑ v : Option M, scaled w (insert f L) i v) =
      ∑ b : M → Fin (Fintype.card I+1),
        if profileWeight w b<p then
          (∏ m, L m ^ (b m).val) * ∏ k, targetCoeff w f block target b k
        else 0 := by
  classical
  rw [by_legal_target_profile w (insert f L) p hR block target
    (fun i m h => by simp [insert, hzero i m h])]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : profileWeight w b < p
  · rw [if_pos hb, if_pos hb]
    have hbase : (∑ x : I → Option M,
        if Legal block target x ∧
          (∀ m, count (fun j : {i : I // block i=target m} => x j.val) m = (b m).val)
        then ∏ i, scaled w f i (x i) else 0) = ∏ k, targetCoeff w f block target b k := by
      simp only [← all_tests block target b]
      simpa only [targetCoeff, Finset.prod_const_one, one_mul] using
        (sum_with_block_test block (test block target b) (scaled w f) (fun _ _ => 1))
    rw [← hbase, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : Legal block target x ∧
        (∀ m, count (fun j : {i : I // block i=target m} => x j.val) m = (b m).val)
    · rw [if_pos hx, if_pos hx]
      have heq := (J6TargetProfile.profile_is_local x block target hx.1 b).mpr hx.2
      have hh (i : I) : scaled w (insert f L) i (x i) =
          scaled w f i (x i) * (x i).elim' 1 L := by simp [scaled, insert, mul_assoc]
      simp only [hh, Finset.prod_mul_distrib, moment_of_choices]
      have hc (m : M) : count x m = (b m).val := congrArg Fin.val (congrFun heq m)
      simp only [hc]
      apply mul_comm
    · rw [if_neg hx, if_neg hx, mul_zero]
  · rw [if_neg hb, if_neg hb]

#print axioms moment_of_choices
#print axioms sum_modes_with_moments
end J6SourceMoment
