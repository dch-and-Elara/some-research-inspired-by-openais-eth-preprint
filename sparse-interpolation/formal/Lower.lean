import ExactDegree
import RingTransfer
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots

open Polynomial

namespace Round4Prefix

open GrenetMcCoy

/-- The variable represents X² in the final witness. -/
noncomputable def squareProduct (n : ℕ) : ℤ[X] :=
  ∏ j ∈ Finset.range n, (X - C (((j : ℤ) + 1) ^ 2))

/-- X times the product of X² - ν² for 1 ≤ ν ≤ n. -/
noncomputable def symmetricWitness (n : ℕ) : ℤ[X] :=
  X * expand ℤ 2 (squareProduct n)

theorem symmetricWitness_eq_product (n : ℕ) :
    symmetricWitness n = X * ∏ j ∈ Finset.range n, (X ^ 2 - C (((j : ℤ) + 1) ^ 2)) := by
  unfold symmetricWitness squareProduct
  rw [map_prod]
  simp only [map_sub, expand_X, expand_C]

theorem symmetricWitness_eval (n : ℕ) (z : ℤ) :
    (symmetricWitness n).eval z = z * ∏ j ∈ Finset.range n, (z ^ 2 - ((j : ℤ) + 1) ^ 2) := by
  rw [symmetricWitness_eq_product, eval_mul, eval_X, eval_prod]
  simp only [eval_sub, eval_pow, eval_X, eval_C]

theorem symmetricWitness_eval_eq_zero_iff (n : ℕ) (z : ℤ) :
    (symmetricWitness n).eval z = 0 ↔ z.natAbs ≤ n := by
  rw [symmetricWitness_eval, mul_eq_zero, Finset.prod_eq_zero_iff]
  constructor
  · rintro (rfl | ⟨j, hj, hzero⟩)
    · simp
    · have hsq : z ^ 2 = ((j : ℤ) + 1) ^ 2 := sub_eq_zero.mp hzero
      have hpow := congrArg Int.natAbs hsq
      have hnat : ((j : ℤ) + 1).natAbs = j + 1 := by
        rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by rw [Nat.cast_add, Nat.cast_one], Int.natAbs_natCast]
      simp only [Int.natAbs_pow, hnat] at hpow
      have he := (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hpow
      rw [he]
      exact Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  · intro h
    by_cases hz : z = 0
    · exact Or.inl hz
    · right
      let j := z.natAbs - 1
      have hpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
      have hj : j + 1 = z.natAbs := by dsimp [j]; omega
      have habs : (z.natAbs : ℤ) = (j : ℤ) + 1 := by exact_mod_cast hj.symm
      refine ⟨j, Finset.mem_range.mpr (by omega), sub_eq_zero.mpr ?_⟩
      rw [← Int.natAbs_pow_two z, habs]

theorem symmetricWitness_ne_zero (n : ℕ) : symmetricWitness n ≠ 0 := by
  intro h
  have hn := (symmetricWitness_eval_eq_zero_iff n ((n + 1 : ℕ) : ℤ)).mp (by simp [h])
  rw [Int.natAbs_natCast] at hn
  omega

/-- The consecutive grid from -n to n, with distinct indices. -/
def symmetricPoint (n : ℕ) (i : Fin (2 * n + 1)) : ℤ :=
  -(n : ℤ) + (i.val : ℤ)

private theorem symmetricPoint_injective (n : ℕ) : Function.Injective (symmetricPoint n) := by
  intro i j h
  apply Fin.ext
  dsimp [symmetricPoint] at h
  omega

/-- Explicitly certify all roots and their distinct count over Z. -/
theorem symmetricWitness_root_set (n : ℕ) :
    (symmetricWitness n).roots.toFinset =
      (Finset.univ : Finset (Fin (2 * n + 1))).image (symmetricPoint n) := by
  ext z
  rw [Multiset.mem_toFinset, mem_roots (symmetricWitness_ne_zero n), IsRoot.def,
    symmetricWitness_eval_eq_zero_iff, Finset.mem_image]
  constructor
  · intro hz
    let j := (z + (n : ℤ)).toNat
    have hcast : (j : ℤ) = z + n := by
      dsimp [j]
      exact Int.toNat_of_nonneg (by omega)
    have hj : j < 2 * n + 1 := by omega
    exact ⟨⟨j, hj⟩, Finset.mem_univ _, by dsimp [symmetricPoint]; omega⟩
  · rintro ⟨i, _, rfl⟩
    have hi := i.isLt
    dsimp [symmetricPoint]
    omega

theorem symmetricWitness_distinct_root_count (n : ℕ) :
    (symmetricWitness n).roots.toFinset.card = 2 * n + 1 := by
  rw [symmetricWitness_root_set, Finset.card_image_of_injective _ (symmetricPoint_injective n)]
  simp

private theorem squareProduct_natDegree (n : ℕ) : (squareProduct n).natDegree = n := by
  unfold squareProduct
  rw [natDegree_prod_of_monic (Finset.range n) (fun j : ℕ => (X : ℤ[X]) - C (((j : ℤ) + 1) ^ 2)) (fun j _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rfl

private theorem support_X_expand_two (p : ℤ[X]) :
    (X * expand ℤ 2 p).support = p.support.image (fun j => 2 * j + 1) := by
  ext i
  cases i with
  | zero =>
    rw [mem_support_iff, coeff_X_mul_zero, Finset.mem_image]
    exact ⟨fun h => False.elim (h rfl), fun ⟨j, _, he⟩ => by omega⟩
  | succ i =>
    rw [mem_support_iff, coeff_X_mul, coeff_expand (by decide : 0 < 2), Finset.mem_image]
    by_cases hi : 2 ∣ i
    · rw [if_pos hi]
      constructor
      · intro hc
        exact ⟨i / 2, mem_support_iff.mpr hc, by omega⟩
      · rintro ⟨j, hj, hEq⟩
        have he : i / 2 = j := by omega
        rw [he]
        exact mem_support_iff.mp hj
    · rw [if_neg hi]
      exact ⟨fun h => False.elim (h rfl), fun ⟨j, _, hEq⟩ =>
        False.elim (hi ⟨j, by omega⟩)⟩

theorem symmetricWitness_support_card_le (n : ℕ) :
    (symmetricWitness n).support.card ≤ n + 1 := by
  rw [symmetricWitness, support_X_expand_two,
    Finset.card_image_of_injective _ (show Function.Injective (fun j : ℕ => 2 * j + 1) from
      fun i j h => by change 2 * i + 1 = 2 * j + 1 at h; omega)]
  have hs : (squareProduct n).support ⊆ Finset.range (n + 1) :=
    supp_subset_range (by rw [squareProduct_natDegree]; omega)
  simpa using Finset.card_le_card hs

/-- The coefficients of the square product alternate strictly in sign
from the leading term down to the constant term. -/
private theorem squareProduct_signed_coeff_pos (n j : ℕ) (hj : j ≤ n) :
    0 < (-1 : ℤ) ^ (n - j) * (squareProduct n).coeff j := by
  induction n generalizing j with
  | zero =>
    have h : j = 0 := by omega
    subst j
    simp [squareProduct]
  | succ n ih =>
    let r : ℤ := ((n : ℤ) + 1) ^ 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hprod : squareProduct (n + 1) = squareProduct n * (X - C r) := by
      simp [squareProduct, Finset.prod_range_succ, r]
    rw [hprod]
    cases j with
    | zero =>
      have he : (squareProduct n * (X - C r)).coeff 0 = -((squareProduct n).coeff 0 * r) := by
        simp [mul_sub]
      rw [he, Nat.sub_zero, pow_succ]
      have h0 := ih 0 (Nat.zero_le n)
      simp only [Nat.sub_zero] at h0
      convert mul_pos h0 hr using 1
      ring
    | succ j =>
      rw [coeff_mul_X_sub_C, Nat.succ_sub_succ_eq_sub]
      have hj' : j ≤ n := Nat.le_of_succ_le_succ hj
      by_cases heq : j = n
      · subst j
        have hc : (squareProduct n).coeff (n + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [squareProduct_natDegree]; omega)
        rw [hc, zero_mul, sub_zero]
        exact ih n le_rfl
      · have hl : j + 1 ≤ n := by omega
        have hpow : (-1 : ℤ) ^ (n - j) = (-1) ^ (n - (j + 1)) * (-1) := by
          rw [← pow_succ]
          congr 1
          omega
        have hsign : (-1 : ℤ) ^ (n - j) * ((squareProduct n).coeff (j + 1) * r) =
            -(((-1 : ℤ) ^ (n - (j + 1)) * (squareProduct n).coeff (j + 1)) * r) := by
          rw [hpow]
          ring
        rw [mul_sub, hsign, sub_neg_eq_add]
        exact add_pos (ih j hj') (mul_pos (ih (j + 1) hl) hr)

private theorem squareProduct_support (n : ℕ) :
    (squareProduct n).support = Finset.range (n + 1) := by
  apply Finset.Subset.antisymm
  · exact supp_subset_range (by rw [squareProduct_natDegree]; omega)
  · intro j hj
    have hpos := squareProduct_signed_coeff_pos n j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    exact mem_support_iff.mpr (fun hzero => by simp [hzero] at hpos)

theorem symmetricWitness_support_card (n : ℕ) :
    (symmetricWitness n).support.card = n + 1 := by
  rw [symmetricWitness, support_X_expand_two,
    Finset.card_image_of_injective _ (show Function.Injective (fun j : ℕ => 2 * j + 1) from
      fun i j h => by change 2 * i + 1 = 2 * j + 1 at h; omega), squareProduct_support, Finset.card_range]

def shortPrefixPoint (t : ℕ) (i : Fin (4 * t - 1)) : ℤ :=
  -((2 * t - 1 : ℕ) : ℤ) + (i.val : ℤ)

/-- Explicit integer sharpness certificate: exactly t terms on each side,
all 4t-1 consecutive samples collide, and the next sample separates them. -/
theorem integer_short_prefix_collision (t : ℕ) (ht : 1 ≤ t) :
    ∃ f g : ℤ[X], f.support.card = t ∧ g.support.card = t ∧ f ≠ g ∧
      f - g = symmetricWitness (2 * t - 1) ∧
      (∀ i : Fin (4 * t - 1), f.eval (shortPrefixPoint t i) = g.eval (shortPrefixPoint t i)) ∧
      f.eval ((2 * t : ℕ) : ℤ) ≠ g.eval ((2 * t : ℕ) : ℤ) := by
  let p := symmetricWitness (2 * t - 1)
  have hcard : p.support.card = 2 * t := by
    dsimp [p]
    rw [symmetricWitness_support_card]
    omega
  obtain ⟨f, g, _, _, hf, hg, hdiff⟩ :=
    exact_support_difference_of_third p.support t ⟨(2 : ℤ), by norm_num, by norm_num⟩
      (by omega) p (Finset.Subset.refl _) hcard.le
  have hne : f ≠ g := by
    intro he
    apply symmetricWitness_ne_zero (2 * t - 1)
    change p = 0
    rw [hdiff, he, sub_self]
  refine ⟨f, g, hf, hg, hne, hdiff.symm, ?_, ?_⟩
  · intro i
    apply sub_eq_zero.mp
    rw [← eval_sub, ← hdiff]
    change (symmetricWitness (2 * t - 1)).eval (shortPrefixPoint t i) = 0
    apply (symmetricWitness_eval_eq_zero_iff _ _).mpr
    have hi := i.isLt
    dsimp [shortPrefixPoint]
    omega
  · intro he
    have hz : (symmetricWitness (2 * t - 1)).eval ((2 * t : ℕ) : ℤ) = 0 := by
      change p.eval ((2 * t : ℕ) : ℤ) = 0
      rw [hdiff, eval_sub, he, sub_self]
    have habs := (symmetricWitness_eval_eq_zero_iff _ _).mp hz
    rw [Int.natAbs_natCast] at habs
    omega

/-- The same collision, with the same support sizes, over Q. -/
theorem rational_short_prefix_collision (t : ℕ) (ht : 1 ≤ t) :
    ∃ f g : ℚ[X], f.support.card = t ∧ g.support.card = t ∧ f ≠ g ∧
      (∀ i : Fin (4 * t - 1),
        f.eval (shortPrefixPoint t i : ℚ) = g.eval (shortPrefixPoint t i : ℚ)) ∧
      f.eval ((2 * t : ℕ) : ℚ) ≠ g.eval ((2 * t : ℕ) : ℚ) := by
  let m := Int.castRingHom ℚ
  have hm : Function.Injective m := Int.cast_injective
  obtain ⟨f, g, hf, hg, hne, _, hobs, hnext⟩ := integer_short_prefix_collision t ht
  have heval (p : ℤ[X]) (z : ℤ) : (p.map m).eval (m z) = m (p.eval z) := by
    rw [eval_map, eval₂_hom]
  refine ⟨f.map m, g.map m, by rwa [support_map_of_injective _ hm],
    by rwa [support_map_of_injective _ hm], (Polynomial.map_injective m hm).ne hne, ?_, ?_⟩
  · intro i
    change (f.map m).eval (m (shortPrefixPoint t i)) = (g.map m).eval (m (shortPrefixPoint t i))
    rw [heval, heval, hobs]
  · intro he
    have he' : (f.map m).eval (m ((2 * t : ℕ) : ℤ)) =
        (g.map m).eval (m ((2 * t : ℕ) : ℤ)) := by simpa [m] using he
    rw [heval, heval] at he'
    exact hnext (hm he')

theorem symmetricWitness_natDegree (n : ℕ) : (symmetricWitness n).natDegree = 2 * n + 1 := by
  have hP : (squareProduct n).Monic := by
    unfold squareProduct
    exact monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have he : (expand ℤ 2 (squareProduct n)).Monic := hP.expand (by decide)
  rw [symmetricWitness, natDegree_mul X_ne_zero he.ne_zero, natDegree_X,
    natDegree_expand, squareProduct_natDegree]
  omega

/-- The distinct roots already exhaust the degree, hence also the root
count with multiplicity. -/
theorem symmetricWitness_root_count (n : ℕ) :
    (symmetricWitness n).roots.card = 2 * n + 1 := by
  apply le_antisymm ((Polynomial.card_roots' _).trans_eq (symmetricWitness_natDegree n))
  rw [← symmetricWitness_distinct_root_count n]
  exact Multiset.toFinset_card_le (symmetricWitness n).roots

theorem sharpWitness_distinct_root_count (t : ℕ) (ht : 1 ≤ t) :
    (symmetricWitness (2 * t - 1)).roots.toFinset.card = 4 * t - 1 := by
  rw [symmetricWitness_distinct_root_count]
  omega

/-- At the same prescribed integer start and regular step 1, every
prefix of length below 4t fails. -/
theorem integer_short_prefix_not_determining (t m : ℕ) (ht : 1 ≤ t) (hm : m < 4 * t) :
    ¬ Round4Transfer.DeterminesUnboundedSparse
      (Round4Transfer.progression (fun i : Fin m => i.val) (-((2 * t - 1 : ℕ) : ℤ)) 1) t := by
  intro h
  obtain ⟨f, g, hf, hg, hne, _, hobs, _⟩ := integer_short_prefix_collision t ht
  apply hne
  refine h f g hf.le hg.le ?_
  intro i
  have hi : i.val < 4 * t - 1 := by have := i.isLt; omega
  simpa [Round4Transfer.progression, shortPrefixPoint] using hobs ⟨i.val, hi⟩

end Round4Prefix
