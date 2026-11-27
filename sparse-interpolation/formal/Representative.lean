import Degree

open scoped BigOperators
open Finset Matrix Polynomial SharpDifference

namespace GrenetResidue

private def sample (a b : ℕ) : Fin (a+b) → ℕ :=
  Fin.addCases (fun i : Fin a => 2*i.val) (fun j : Fin b => 2*j.val+1)

private theorem sample_injective (a b : ℕ) : Function.Injective (sample a b) := by
  intro i j
  refine Fin.addCases (motive := fun i => sample a b i = sample a b j → i = j) ?_ ?_ i
  · intro x
    refine Fin.addCases (motive := fun j => sample a b (Fin.castAdd b x) = sample a b j →
      Fin.castAdd b x = j) ?_ ?_ j
    · intro y he
      simp [sample] at he
      exact congrArg (Fin.castAdd b) (Fin.ext he)
    · intro y he
      simp [sample] at he
      omega
  · intro x
    refine Fin.addCases (motive := fun j => sample a b (Fin.natAdd a x) = sample a b j →
      Fin.natAdd a x = j) ?_ ?_ j
    · intro y he
      simp [sample] at he
      omega
    · intro y he
      simp [sample] at he
      exact congrArg (Fin.natAdd a) (Fin.ext he)

private theorem sample_oddSize (a b : ℕ) : oddSize (sample a b) = b := by
  classical
  let e : Fin b ≃ {j // Odd (sample a b j)} :=
    { toFun := fun i => ⟨Fin.natAdd a i, by simp [sample]⟩
      invFun := fun j => ⟨j.val.val - a, by
        have hi : a ≤ j.val.val := by
          by_contra! hh
          let i : Fin a := ⟨j.val.val, hh⟩
          have he : Fin.castAdd b i = j.val := Fin.ext rfl
          have hp := j.property
          rw [← he] at hp
          simp [sample, Nat.odd_iff] at hp
        have hj := j.val.isLt
        omega⟩
      left_inv := fun i => by
        apply Fin.ext
        simp
      right_inv := fun j => by
        apply Subtype.ext
        apply Fin.ext
        have hi : a ≤ j.val.val := by
          by_contra! hh
          let i : Fin a := ⟨j.val.val, hh⟩
          have he : Fin.castAdd b i = j.val := Fin.ext rfl
          have hp := j.property
          rw [← he] at hp
          simp [sample, Nat.odd_iff] at hp
        change a + (j.val.val - a) = j.val.val
        omega }
  exact (Fintype.card_congr e).symm.trans (Fintype.card_fin _)

private theorem sum_twice (n : ℕ) : (∑ j : Fin n, 2*j.val) + n = n*n := by
  rw [Fin.sum_univ_eq_sum_range (fun j => 2*j) n, ← Finset.mul_sum]
  have hh := Finset.sum_range_id_mul_two n
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.succ_sub_one] at hh
    nlinarith

private theorem sum_sample (a b : ℕ) :
    (∑ i, sample a b i) + a = a*a + b*b := by
  rw [Fin.sum_univ_add]
  simp only [sample, Fin.addCases_left, Fin.addCases_right, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]
  have ha := sum_twice a
  have hb := sum_twice b
  omega

/-- The smallest b odd exponents and the smallest h+m even exponents, with h=b+m. -/
def representative (b m : ℕ) : Fin (2*(b+m)) → ℕ :=
  fun j => sample (b+2*m) b (Fin.cast (by omega : 2*(b+m) = (b+2*m)+b) j)

theorem representative_injective (b m : ℕ) : Function.Injective (representative b m) :=
  (sample_injective (b+2*m) b).comp (Fin.cast_injective _)

theorem representative_oddSize (b m : ℕ) : oddSize (representative b m) = b := by
  classical
  let e : {j // Odd (representative b m j)} ≃ {j // Odd (sample (b+2*m) b j)} :=
    (finCongr (by omega : 2*(b+m) = (b+2*m)+b)).subtypeEquiv (fun _ => Iff.rfl)
  exact (Fintype.card_congr e).trans (sample_oddSize _ _)

theorem representative_minority (b m : ℕ) : minority (representative b m) = b := by
  unfold minority
  have h := evenSize_add_oddSize (representative b m)
  rw [representative_oddSize] at h ⊢
  omega

theorem representative_deficit (b m : ℕ) : deficit (b+m) (representative b m) = m := by
  rw [deficit, representative_minority]
  omega

theorem representative_sum (b m : ℕ) :
    (∑ j, representative b m j) = (2*(b+m)).choose 2 + m^2 + m*(m-1) := by
  have hs := sum_sample (b+2*m) b
  have he : (∑ j, representative b m j) = ∑ j, sample (b+2*m) b j :=
    Fintype.sum_equiv (finCongr (by omega : 2*(b+m) = (b+2*m)+b)) _ _ (fun _ => rfl)
  have hd (k : ℕ) : 2*k.choose 2 + k = k*k := by
    rw [Nat.choose_two_right, ← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i : ℕ => i) k]
    rw [Finset.mul_sum]
    exact sum_twice k
  have hm : m*(m-1)+m = m*m := by
    cases m with
    | zero => simp
    | succ m => simp only [Nat.succ_sub_one]; ring
  rw [he]
  have hc := hd (2*(b+m))
  nlinarith [hs, hc, hm]

theorem representative_factor_exact (b m : ℕ) :
    liftPoly (normalized (representative b m)) = allFactorsQ (representative b m) := by
  let E := representative b m
  have hE := representative_injective b m
  obtain ⟨q, hq⟩ := allFactorsQ_dvd E hE
  have hc := lift_normalized_eval_zero E hE
  have hq0 : q.eval 0 = 1 := by
    rw [hq, Polynomial.eval_mul, allFactorsQ_eval_zero, one_mul] at hc
    exact hc
  have hqn : q ≠ 0 := by intro hz; simp [hz] at hq0
  have hfn : allFactorsQ E ≠ 0 := by
    intro hz
    have hz' := allFactorsQ_eval_zero E
    simp [hz] at hz'
  have hd := natDegree_lift_normalized_bound E hE
  rw [hq, Polynomial.natDegree_mul hfn hqn, allFactorsQ_natDegree, representative_sum,
    representative_deficit] at hd
  have hc0 : q.natDegree = 0 := by omega
  have hq1 : q = 1 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hc0] at hq0 ⊢
    simpa using congrArg Polynomial.C hq0
  simpa [E, hq1] using hq

end GrenetResidue

