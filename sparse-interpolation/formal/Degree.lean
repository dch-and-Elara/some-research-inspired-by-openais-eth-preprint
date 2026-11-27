import Factor

open scoped BigOperators
open Finset Matrix Polynomial SharpDifference

namespace GrenetResidue

def centerSet (k : ℕ) : Finset ℕ := (Finset.range (2*k)).erase 0

noncomputable def allFactorsQ {k : ℕ} (E : Fin k → ℕ) : UPoly :=
  ∏ s ∈ centerSet k, linearQ s ^ multiplicity E s

noncomputable def oddFactors (h : ℕ) (E : Fin (2*h) → ℕ) : LocalPoly :=
  ∏ j ∈ Finset.range (2*h), linear (2*j+1) ^ multiplicity E (2*j+1)

noncomputable def evenFactors (h : ℕ) (E : Fin (2*h) → ℕ) : LocalPoly :=
  ∏ j ∈ Finset.range (2*h), linear (2*j) ^ multiplicity E (2*j)

theorem allFactorsQ_dvd {k : ℕ} (E : Fin k → ℕ) (hE : Function.Injective E) :
    allFactorsQ E ∣ liftPoly (normalized E) := by
  exact all_factors_dvd E hE (centerSet k)
    (fun s hs => Nat.pos_of_ne_zero (Finset.mem_erase.mp hs).1)

private theorem aggregate_split {A : Type*} [CommMonoid A] (f : ℕ → A) (k : ℕ) :
    (∏ s ∈ Finset.range (2*k), f s) =
      (∏ j ∈ Finset.range k, f (2*j+1)) * ∏ j ∈ Finset.range k, f (2*j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = (2*k+1)+1 by omega, Finset.prod_range_succ, Finset.prod_range_succ,
      ih, Finset.prod_range_succ, Finset.prod_range_succ]
    ac_rfl

theorem allFactorsQ_split (h : ℕ) (E : Fin (2*h) → ℕ) :
    allFactorsQ E = liftPoly (oddFactors h E * evenFactors h E) := by
  unfold allFactorsQ centerSet oddFactors evenFactors
  rw [Finset.prod_erase (f := fun s => linearQ s ^ multiplicity E s) _ (by simp [linearQ]),
    aggregate_split, map_mul, map_prod, map_prod]
  simp only [map_pow, lift_linear]

private theorem sum_centers_split (f : ℕ → ℕ) (k : ℕ) :
    (∑ s ∈ Finset.range (2*k), f s) =
      (∑ j ∈ Finset.range k, f (2*j+1)) + ∑ j ∈ Finset.range k, f (2*j) :=
  @aggregate_split (Multiplicative ℕ) _ f k

theorem sum_center_multiplicities (h : ℕ) (E : Fin (2*h) → ℕ) (eps : ℕ) (heps : eps ≤ 1) :
    (∑ j ∈ Finset.range (2*h), multiplicity E (2*j+eps)) =
      if eps = 1 then (deficit h E)^2 else (deficit h E)*(deficit h E-1) := by
  let b := minority E
  let m := deficit h E
  have hb := minority_le E
  have he : b + m = h := Nat.add_sub_of_le hb
  have hh := HalfBlockCount.all_centers b m eps heps
  rw [he] at hh
  exact hh

theorem linearQ_natDegree {s : ℕ} (hs : 0 < s) : (linearQ s).natDegree = 1 := by
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  rw [linearQ, add_comm, ← C_1, natDegree_add_C, natDegree_C_mul_X _ hs0]

theorem linearQ_ne_zero (s : ℕ) : linearQ s ≠ 0 := by
  intro h
  have h0 := congrArg (eval (0 : ℚ)) h
  norm_num [linearQ] at h0

private theorem multiplicity_zero {k : ℕ} (E : Fin k → ℕ) : multiplicity E 0 = 0 := by
  simp [multiplicity, HalfBlockCount.pairs_card]

theorem allFactorsQ_natDegree (h : ℕ) (E : Fin (2*h) → ℕ) :
    (allFactorsQ E).natDegree = (deficit h E)^2 + (deficit h E)*(deficit h E-1) := by
  unfold allFactorsQ
  rw [Polynomial.natDegree_prod _ _ (fun s _ => pow_ne_zero _ (linearQ_ne_zero s))]
  calc
    _ = ∑ s ∈ centerSet (2*h), multiplicity E s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Polynomial.natDegree_pow, linearQ_natDegree (Nat.pos_of_ne_zero (Finset.mem_erase.mp hs).1),
        mul_one]
    _ = _ := by
      unfold centerSet
      rw [Finset.sum_erase (f := multiplicity E) _ (multiplicity_zero E), sum_centers_split]
      have ho := sum_center_multiplicities h E 1 (by decide)
      have he := sum_center_multiplicities h E 0 (by decide)
      simp at ho
      simp only [Nat.add_zero, Nat.zero_ne_one, if_false] at he
      rw [ho, he]

private theorem linearQ_eval_zero (s : ℕ) : (linearQ s).eval 0 = 1 := by
  simp [linearQ]

theorem allFactorsQ_eval_zero {k : ℕ} (E : Fin k → ℕ) :
    (allFactorsQ E).eval 0 = 1 := by
  change (Polynomial.evalRingHom 0) _ = _
  simp [allFactorsQ, linearQ_eval_zero, map_prod]

theorem natDegree_source_det_le {k : ℕ} (E : Fin k → ℕ) :
    (sourceMatrix E).det.natDegree ≤ ∑ i, E i := by
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hz (z : ℤ) : (z : UPoly) = C (z : ℚ) := (Polynomial.C_eq_intCast (R := ℚ) z).symm
  rw [hz]
  refine (Polynomial.natDegree_C_mul_le ..).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  have hbase : (1 + ((σ i).val : UPoly) * twoU).natDegree ≤ 1 := by
    unfold twoU
    rw [← mul_assoc]
    have he : ((σ i).val : UPoly) * 2 = C (((σ i).val : ℚ) * 2) := by
      rw [map_mul, Polynomial.C_eq_natCast]
      have ht : C (2 : ℚ) = (2 : UPoly) := Polynomial.C_eq_natCast (R := ℚ) 2
      rw [ht]
    rw [he, add_comm, ← C_1, natDegree_add_C]
    exact (Polynomial.natDegree_C_mul_le ..).trans (by simp)
  change ((1 + ((σ i).val : UPoly) * twoU) ^ E i).natDegree ≤ E i
  rw [Polynomial.natDegree_pow]
  simpa using Nat.mul_le_mul_left (E i) hbase


theorem eval_liftPoly_zero (p : LocalPoly) : (liftPoly p).eval 0 = toRat (atZero p) := by
  change (p.map toRat).eval 0 = toRat (p.eval 0)
  rw [Polynomial.eval_map, ← map_zero toRat, Polynomial.eval₂_hom]

theorem lift_normalized_eval_zero {k : ℕ} (E : Fin k → ℕ) (hE : Function.Injective E) :
    (liftPoly (normalized E)).eval 0 = 1 := by
  rw [eval_liftPoly_zero, normalized_at_zero E hE, map_one]

theorem natDegree_lift_normalized_bound {k : ℕ} (E : Fin k → ℕ)
    (hE : Function.Injective E) :
    k.choose 2 + (liftPoly (normalized E)).natDegree ≤ ∑ i, E i := by
  have hN : liftPoly (normalized E) ≠ 0 := by
    intro hh
    have h0 := lift_normalized_eval_zero E hE
    simp [hh] at h0
  have hV : exponentV E ≠ 0 := by
    intro hh
    have hev : liftPoly ((Matrix.vandermonde fun j => (E j : LocalPoly)).det) = 0 := hh
    have ha : Function.Injective liftPoly := Polynomial.map_injective _ Subtype.val_injective
    rw [← map_zero liftPoly] at hev
    exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (fun _ _ he => hE (Nat.cast_injective he)) (ha hev)
  have hU : twoU ≠ 0 := mul_ne_zero (by norm_num) X_ne_zero
  have hdU : twoU.natDegree = 1 := by
    unfold twoU
    rw [show (2 : UPoly) = C (2 : ℚ) from (Polynomial.C_eq_natCast (R := ℚ) 2).symm,
      natDegree_C_mul_X _ (by norm_num)]
  have hb := natDegree_source_det_le E
  rw [normalized_factorization, Polynomial.natDegree_mul (mul_ne_zero (pow_ne_zero _ hU) hV) hN,
    Polynomial.natDegree_mul (pow_ne_zero _ hU) hV, Polynomial.natDegree_pow, hdU, mul_one] at hb
  omega

end GrenetResidue

