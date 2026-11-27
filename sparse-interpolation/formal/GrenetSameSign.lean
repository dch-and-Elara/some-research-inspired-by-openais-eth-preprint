import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Polynomial Matrix
open scoped BigOperators

namespace GrenetSameSign

private theorem support_shift_card (p : ℝ[X]) (m : ℕ) :
    (p * X ^ m).support.card = p.support.card := by
  classical
  have h : (p * X ^ m).support = p.support.image (fun i => i + m) := by
    ext j
    rw [Finset.mem_image, mem_support_iff, coeff_mul_X_pow']
    by_cases hj : m ≤ j
    · rw [if_pos hj]
      constructor
      · intro hn
        exact ⟨j-m, mem_support_iff.mpr hn, by omega⟩
      · rintro ⟨a, ha, rfl⟩
        simpa using mem_support_iff.mp ha
    · rw [if_neg hj]
      simp only [ne_eq, not_true_eq_false, false_iff]
      rintro ⟨a, _, ha⟩
      omega
  rw [h, Finset.card_image_of_injective]
  exact fun i j hij => Nat.add_right_cancel hij

private theorem derivative_support_lt {p : ℝ[X]} (h : p.coeff 0 ≠ 0) :
    p.derivative.support.card < p.support.card := by
  classical
  have hsub : p.derivative.support.image Nat.succ ⊆ p.support.erase 0 := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_erase.mpr ⟨Nat.succ_ne_zero _, of_mem_support_derivative hi⟩
  have hi := Finset.card_mono hsub
  rw [Finset.card_image_of_injective _ Nat.succ_injective,
    Finset.card_erase_of_mem (mem_support_iff.mpr h)] at hi
  have hp : 0 < p.support.card := Finset.card_pos.mpr ⟨0, mem_support_iff.mpr h⟩
  omega

/-- A nonzero real polynomial has fewer distinct positive roots than nonzero terms.
The finite-set form needs no ordering or multiplicity assumptions on the roots. -/
theorem card_lt_support_of_positive_roots (p : ℝ[X]) (hp : p ≠ 0)
    (s : Finset ℝ) (hpos : ∀ x ∈ s, 0 < x) (hzero : ∀ x ∈ s, p.eval x = 0) :
    s.card < p.support.card := by
  classical
  generalize hk : p.support.card = k
  induction k using Nat.strong_induction_on generalizing p s with
  | h k ih =>
    let m := p.natTrailingDegree
    obtain ⟨q, hq⟩ : X ^ m ∣ p :=
      X_pow_dvd_iff.mpr fun _ hi => coeff_eq_zero_of_lt_natTrailingDegree hi
    have hshift : p = q * X ^ m := hq.trans (mul_comm _ _)
    have hqc : q.coeff 0 ≠ 0 := by
      have hn := coeff_natTrailingDegree_ne_zero.mpr hp
      change p.coeff m ≠ 0 at hn
      rw [hshift] at hn
      have he := coeff_mul_X_pow q m 0
      rw [zero_add] at he
      rwa [he] at hn
    have hcard : q.support.card = k := by
      rw [hshift, support_shift_card] at hk
      exact hk
    have hqzero (x : ℝ) (hx : x ∈ s) : q.eval x = 0 := by
      have hz := hzero x hx
      rw [hshift, eval_mul, eval_pow, eval_X] at hz
      exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ (hpos x hx).ne')
    by_cases hd : q.derivative = 0
    · have hs : s = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hv := hqzero x hx
        rw [eq_C_of_derivative_eq_zero hd, eval_C] at hv
        exact hqc hv
      rw [hs, Finset.card_empty, ← hcard]
      exact Finset.card_pos.mpr ⟨0, mem_support_iff.mpr hqc⟩
    · let r := q.derivative.roots.toFinset.filter fun x => 0 < x
      have hr : s.card ≤ r.card + 1 := by
        refine Finset.card_le_of_interleaved fun x hx y hy hxy _ => ?_
        obtain ⟨z, hz, hdv⟩ :=
          exists_deriv_eq_zero hxy q.continuousOn ((hqzero x hx).trans (hqzero y hy).symm)
        refine ⟨z, Finset.mem_filter.mpr ⟨?_, (hpos x hx).trans hz.1⟩, hz.1, hz.2⟩
        rwa [Multiset.mem_toFinset, mem_roots hd, IsRoot, ← q.deriv]
      have hds := derivative_support_lt hqc
      rw [hcard] at hds
      have hri := ih q.derivative.support.card hds q.derivative hd r
        (fun x hx => (Finset.mem_filter.mp hx).2)
        (fun x hx => (mem_roots hd).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hx).1))
        rfl
      omega

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_pow_ne_zero_positive (x : ι → ℝ) (e : ι → ℕ)
    (hx : Function.Injective x) (he : Function.Injective e) (hp : ∀ i, 0 < x i) :
    (Matrix.of fun i j => x i ^ e j).det ≠ 0 := by
  classical
  let A : Matrix ι ι ℝ := Matrix.of fun i j => x i ^ e j
  change A.det ≠ 0
  by_contra hdet
  have hni : ¬ Function.Injective A.mulVec := by
    intro hinj
    exact not_isUnit_zero (hdet ▸ (Matrix.isUnit_iff_isUnit_det A).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hinj))
  obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hni
  let c : ι → ℝ := u-v
  have hc : c ≠ 0 := sub_ne_zero.mpr hne
  let p : ℝ[X] := ∑ i, monomial (e i) (c i)
  have hcoeff (i : ι) : p.coeff (e i) = c i := by
    change (∑ j, monomial (e j) (c j)).coeff (e i) = c i
    rw [finset_sum_coeff, Finset.sum_eq_single i]
    · exact coeff_monomial_same _ _
    · intro j _ hji
      exact coeff_monomial_of_ne _ (fun hij => hji (he hij.symm))
    · simp
  have hp0 : p ≠ 0 := by
    intro h
    apply hc
    funext i
    simpa using (hcoeff i).symm.trans (by rw [h, coeff_zero])
  have hs : p.support ⊆ Finset.univ.image e := by
    intro j hj
    by_contra nh
    apply mem_support_iff.mp hj
    change (∑ i, monomial (e i) (c i)).coeff j = 0
    rw [finset_sum_coeff]
    exact Finset.sum_eq_zero fun i _ => coeff_monomial_of_ne _ (fun hij =>
      nh (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hij.symm⟩))
  have hsize : p.support.card ≤ Fintype.card ι :=
    (Finset.card_mono hs).trans (Finset.card_image_le.trans_eq Finset.card_univ)
  have hker : A.mulVec c = 0 := by
    change A.mulVec (u - v) = 0
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hz (i : ι) : p.eval (x i) = 0 := by
    have hv := congrFun hker i
    simpa [p, A, Matrix.mulVec, dotProduct, eval_finset_sum, eval_monomial, mul_comm] using hv
  have hroots := card_lt_support_of_positive_roots p hp0 (Finset.univ.image x)
    (fun y hy => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy; exact hp i)
    (fun y hy => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy; exact hz i)
  rw [Finset.card_image_of_injective _ hx, Finset.card_univ] at hroots
  omega

/-- A generalized Vandermonde matrix of distinct strictly same-sign real nodes is nonsingular. -/
theorem det_pow_ne_zero_real (x : ι → ℝ) (e : ι → ℕ)
    (hx : Function.Injective x) (he : Function.Injective e)
    (h : (∀ i, 0 < x i) ∨ (∀ i, x i < 0)) :
    (Matrix.of fun i j => x i ^ e j).det ≠ 0 := by
  rcases h with hp | hn
  · exact det_pow_ne_zero_positive x e hx he hp
  · have hpos := det_pow_ne_zero_positive (fun i => -x i) e
      (fun _ _ hij => hx (neg_injective hij)) he (fun i => neg_pos.mpr (hn i))
    intro hz
    apply hpos
    have hA : (Matrix.of fun i j => (-x i) ^ e j) =
        (Matrix.of fun i j => x i ^ e j) *
          Matrix.diagonal (fun j => (-1 : ℝ) ^ e j) := by
      ext i j
      rw [Matrix.mul_diagonal]
      change (-x i) ^ e j = x i ^ e j * (-1 : ℝ) ^ e j
      rw [← mul_pow, mul_neg, mul_one]
    rw [hA, Matrix.det_mul, hz, zero_mul]

/-- The same-sign nonsingularity theorem over the rationals. -/
theorem det_pow_ne_zero_rat (x : ι → ℚ) (e : ι → ℕ)
    (hx : Function.Injective x) (he : Function.Injective e)
    (h : (∀ i, 0 < x i) ∨ (∀ i, x i < 0)) :
    (Matrix.of fun i j => x i ^ e j).det ≠ 0 := by
  have hs : (∀ i, 0 < (x i : ℝ)) ∨ (∀ i, (x i : ℝ) < 0) := by
    rcases h with hp | hn
    · exact Or.inl fun i => by exact_mod_cast hp i
    · exact Or.inr fun i => by exact_mod_cast hn i
  have ht := det_pow_ne_zero_real (fun i => (x i : ℝ)) e
    (Rat.cast_injective.comp hx) he hs
  intro hz
  apply ht
  have hm := congrArg (Rat.castHom ℝ) hz
  rw [RingHom.map_det, map_zero] at hm
  have heq : (Rat.castHom ℝ).mapMatrix (Matrix.of fun i j => x i ^ e j) =
      (Matrix.of fun i j => (x i : ℝ) ^ e j) := by
    ext i j
    exact map_pow (Rat.castHom ℝ) (x i) (e j)
  rw [heq] at hm
  exact hm

end Matrix
end GrenetSameSign
