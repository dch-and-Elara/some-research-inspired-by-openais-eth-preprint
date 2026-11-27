import ParityReduction
import RationalPairs
import PairCount
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators

open scoped BigOperators
open Finset Matrix Polynomial SharpDifference

namespace GrenetResidue

private theorem coprime_unit {R : Type*} [CommRing R] {a b : R} (ha : IsUnit a) :
    IsCoprime a b := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨↑u⁻¹, 0, by simp⟩

noncomputable def symbolicQ (M k : ℕ) : MvPolynomial (Fin k) LocalPoly :=
  (common_symbolic_normalization M k).choose

noncomputable def cutoff {k : ℕ} (E : Fin k → ℕ) : ℕ :=
  Finset.univ.sup E

theorem le_cutoff {k : ℕ} (E : Fin k → ℕ) (j : Fin k) : E j ≤ cutoff E :=
  Finset.le_sup (f := E) (Finset.mem_univ j)

noncomputable def normalized {k : ℕ} (E : Fin k → ℕ) : LocalPoly :=
  MvPolynomial.eval (fun j => (E j : LocalPoly)) (symbolicQ (cutoff E) k)

noncomputable def exponentV {k : ℕ} (E : Fin k → ℕ) : UPoly :=
  liftPoly ((Matrix.vandermonde (fun j => (E j : LocalPoly))).det)

theorem liftPoly_injective : Function.Injective liftPoly :=
  Polynomial.map_injective _ Subtype.val_injective

theorem exponentV_ne_zero {k : ℕ} {E : Fin k → ℕ} (hE : Function.Injective E) :
    exponentV E ≠ 0 := by
  apply fun h => Matrix.det_vandermonde_ne_zero_iff.mpr
    (fun _ _ he => hE (Nat.cast_injective he)) (liftPoly_injective (h.trans (map_zero liftPoly).symm))

theorem normalized_factorization {k : ℕ} (E : Fin k → ℕ) :
    (sourceMatrix E).det = twoU ^ k.choose 2 * exponentV E * liftPoly (normalized E) :=
  (common_symbolic_normalization (cutoff E) k).choose_spec.2.1 E (le_cutoff E)

theorem normalized_at_zero {k : ℕ} (E : Fin k → ℕ) (hE : Function.Injective E) :
    atZero (normalized E) = 1 :=
  (common_symbolic_normalization (cutoff E) k).choose_spec.2.2.2 E hE (le_cutoff E)

theorem normalized_eq_common {k M : ℕ} (E : Fin k → ℕ) (hE : Function.Injective E)
    (hM : ∀ j, E j ≤ M) :
    normalized E = MvPolynomial.eval (fun j => (E j : LocalPoly)) (symbolicQ M k) := by
  apply liftPoly_injective
  have hc : twoU ≠ 0 := mul_ne_zero (by norm_num) X_ne_zero
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hc) (exponentV_ne_zero hE))
  exact (normalized_factorization E).symm.trans
    ((common_symbolic_normalization M k).choose_spec.2.1 E hM)

theorem normalized_same_odd_count {k : ℕ} (E F : Fin k → ℕ)
    (hE : Function.Injective E) (hF : Function.Injective F) (h : oddCount E = oddCount F) :
    reducePoly (normalized E) = reducePoly (normalized F) := by
  let M := max (cutoff E) (cutoff F)
  rw [normalized_eq_common E hE (M := M) (fun j => (le_cutoff E j).trans (le_max_left _ _)),
      normalized_eq_common F hF (M := M) (fun j => (le_cutoff F j).trans (le_max_right _ _))]
  exact (common_symbolic_normalization M k).choose_spec.2.2.1 E F h

noncomputable def oddSize {k : ℕ} (E : Fin k → ℕ) : ℕ := Fintype.card {j // Odd (E j)}
noncomputable def evenSize {k : ℕ} (E : Fin k → ℕ) : ℕ := Fintype.card {j // Even (E j)}
noncomputable def minority {k : ℕ} (E : Fin k → ℕ) : ℕ := min (evenSize E) (oddSize E)
noncomputable def deficit (h : ℕ) (E : Fin (2*h) → ℕ) : ℕ := h - minority E

theorem oddSize_eq_oddCount {k : ℕ} (E : Fin k → ℕ) : oddSize E = oddCount E := by
  classical
  let e : {j // Odd (E j)} ≃ ↥(Finset.univ.filter (fun j => E j % 2 = 1)) :=
    Equiv.subtypeEquivRight (fun j => by simp [Nat.odd_iff])
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem evenSize_add_oddSize {k : ℕ} (E : Fin k → ℕ) : evenSize E + oddSize E = k := by
  classical
  let e := Equiv.sumCompl (fun j : Fin k => Even (E j))
  let e' : {j // ¬ Even (E j)} ≃ {j // Odd (E j)} :=
    Equiv.subtypeEquivRight (fun _ => Nat.not_even_iff_odd)
  have hh := Fintype.card_congr e
  rw [Fintype.card_sum, Fintype.card_congr e', Fintype.card_fin] at hh
  exact hh

theorem minority_le {h : ℕ} (E : Fin (2*h) → ℕ) : minority E ≤ h := by
  have hh := evenSize_add_oddSize E
  unfold minority
  omega

theorem sumPairs_card (k s : ℕ) :
    Fintype.card (SharpFactor.SumPairs k s) = (HalfBlockCount.pairs k s).card := by
  classical
  let e : SharpFactor.SumPairs k s ≃ ↥(HalfBlockCount.pairs k s) :=
    { toFun := fun a => ⟨a.val.1.val, by
        have ha := a.property
        have h₂ : s - a.val.1.val = a.val.2.val := by omega
        simp [HalfBlockCount.pairs, a.val.1.isLt, h₂, ha.1, a.val.2.isLt]⟩
      invFun := fun i => by
        have hi := i.property
        simp only [HalfBlockCount.pairs, Finset.mem_filter, Finset.mem_range] at hi
        exact ⟨(⟨i, hi.1⟩, ⟨s-i, hi.2.2⟩), hi.2.1, by change i.val + (s-i.val) = s; have hh := hi.2.1; omega⟩
      left_inv := fun a => by
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          rfl
        · apply Fin.ext
          have h := a.property.2
          change s - a.val.1.val = a.val.2.val
          omega
      right_inv := fun i => Subtype.ext rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

noncomputable def multiplicity {k : ℕ} (E : Fin k → ℕ) (s : ℕ) : ℕ :=
  (HalfBlockCount.pairs k s).card - minority E

noncomputable def linear (s : ℕ) : LocalPoly := 1 + C (s : D) * X
noncomputable def linearQ (s : ℕ) : UPoly := 1 + C (s : ℚ) * X

@[simp] theorem lift_linear (s : ℕ) : liftPoly (linear s) = linearQ s := by
  simp [linear, linearQ, liftPoly]

theorem linearQ_mul_scale (s : ℕ) (hs : 0 < s) :
    linearQ s = C (s : ℚ) * (X - C (-((s : ℚ)⁻¹))) := by
  have hn : (s : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  rw [linearQ, mul_sub, ← map_mul, mul_neg, mul_inv_cancel₀ hn, map_neg, map_one]
  ring

theorem linearQ_coprime {s t : ℕ} (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t) :
    IsCoprime (linearQ s) (linearQ t) := by
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have ht0 : (t : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ht
  have hst0 : (s : ℚ) ≠ (t : ℚ) := by exact_mod_cast hst
  have hd : IsUnit ((-((s : ℚ)⁻¹)) - (-((t : ℚ)⁻¹))) := by
    apply isUnit_iff_ne_zero.mpr
    intro hh
    apply hst0
    simpa using inv_injective (neg_injective (sub_eq_zero.mp hh))
  rw [linearQ_mul_scale s hs, linearQ_mul_scale t ht]
  simpa only [mul_comm (C (s : ℚ)), mul_comm (C (t : ℚ))] using (((Polynomial.isCoprime_X_sub_C_of_isUnit_sub hd).mul_left
      (coprime_unit ((isUnit_iff_ne_zero.mpr hs0).map Polynomial.C))).mul_right
      (coprime_unit ((isUnit_iff_ne_zero.mpr ht0).map Polynomial.C)).symm)

theorem linearQ_coprime_X {s : ℕ} : IsCoprime (linearQ s) X := by
  refine ⟨1, -C (s : ℚ), ?_⟩
  simp [linearQ, add_assoc]

theorem sourceMatrix_eq_halfSample {k : ℕ} (E : Fin k → ℕ) :
    sourceMatrix E = SharpFactor.halfSampleMatrix E := by
  apply Matrix.ext
  intro i j
  simp only [sourceMatrix, SharpFactor.halfSampleMatrix, Matrix.of_apply, twoU]
  rw [map_mul, Polynomial.C_eq_natCast]
  have ht : C (2 : ℚ) = (2 : UPoly) := Polynomial.C_eq_natCast (R := ℚ) 2
  rw [ht]
  congr 1
  ring

theorem exponentV_isUnit {k : ℕ} {E : Fin k → ℕ} (hE : Function.Injective E) :
    IsUnit (exponentV E) := by
  have hp : exponentV E =
      C ((Matrix.vandermonde (fun j => (E j : ℚ))).det) := by
    unfold exponentV
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    change liftPoly ((E i : LocalPoly) ^ j.val) = C ((E i : ℚ) ^ j.val)
    simp
  rw [hp]
  exact (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr
    (fun _ _ he => hE (Nat.cast_injective he)))).map Polynomial.C

theorem factor_dvd_normalized {k s : ℕ} (hs : 0 < s) (E : Fin k → ℕ)
    (hE : Function.Injective E) : linearQ s ^ multiplicity E s ∣ liftPoly (normalized E) := by
  have hd := SharpFactor.halfSample_factor hs E
  rw [← sourceMatrix_eq_halfSample, normalized_factorization] at hd
  change linearQ s ^ (Fintype.card (SharpFactor.SumPairs k s) - minority E) ∣ _ at hd
  rw [sumPairs_card, mul_assoc] at hd
  have ht : twoU = C (2 : ℚ) * X := by
    unfold twoU
    rw [show C (2 : ℚ) = (2 : UPoly) from Polynomial.C_eq_natCast (R := ℚ) 2]
  have hc : IsCoprime (linearQ s) twoU := by
    rw [ht, mul_comm]
    exact (linearQ_coprime_X (s := s)).mul_right
      (coprime_unit ((isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map Polynomial.C)).symm
  exact ((coprime_unit (exponentV_isUnit hE)).symm.pow_left).dvd_of_dvd_mul_left
    ((hc.pow).dvd_of_dvd_mul_left hd)

/-- Simultaneous extraction, for any finite set of positive centers. -/
theorem all_factors_dvd {k : ℕ} (E : Fin k → ℕ) (hE : Function.Injective E) (S : Finset ℕ)
    (hs : ∀ s ∈ S, 0 < s) :
    (∏ s ∈ S, linearQ s ^ multiplicity E s) ∣ liftPoly (normalized E) := by
  apply Finset.prod_dvd_of_coprime
  · intro s hsm t htm hst
    exact (linearQ_coprime (hs s hsm) (hs t htm) hst).pow
  · exact fun s hm => factor_dvd_normalized (hs s hm) E hE

end GrenetResidue

