import Lower
import Mathlib.RingTheory.Polynomial.ScaleRoots

open Polynomial
open GrenetMcCoy Round4Transfer Round4Prefix

namespace GrenetPaper

variable {R : Type*} [CommRing R] [Nontrivial R] [IsAddTorsionFree R]

private theorem castInt_injective : Function.Injective (Int.castRingHom R) := by
  apply (injective_iff_map_eq_zero (Int.castRingHom R)).mpr
  intro n hn
  by_contra hne
  have h : n • (1 : R) = n • (0 : R) := by
    simpa [Int.castRingHom, zsmul_eq_mul] using hn
  exact one_ne_zero (zsmul_right_injective hne h)

noncomputable def scaledWitness (n : ℕ) (b : R) : R[X] :=
  ((symmetricWitness n).map (Int.castRingHom R)).scaleRoots b

theorem scaledWitness_support (n : ℕ) (b : R) (hb : b ∈ nonZeroDivisors R) :
    (scaledWitness n b).support.card = n + 1 := by
  rw [scaledWitness, support_scaleRoots_eq _ hb,
    support_map_of_injective _ castInt_injective, symmetricWitness_support_card]

theorem scaledWitness_eval (n : ℕ) (b : R) (z : ℤ) :
    (scaledWitness n b).eval ((z : R) * b) =
      b ^ (2 * n + 1) * (((symmetricWitness n).eval z : ℤ) : R) := by
  let m := Int.castRingHom R
  let p := (symmetricWitness n).map m
  have h := scaleRoots_eval₂_mul (p := p) (RingHom.id R) (m z) b
  change (scaledWitness n b).eval ((z : R) * b) = _
  rw [mul_comm, scaledWitness]
  change (p.scaleRoots b).eval (b * m z) = b ^ (2 * n + 1) * m ((symmetricWitness n).eval z)
  simp only [RingHom.id_apply, eval₂_id] at h
  rw [h, show p.natDegree = 2 * n + 1 by
    rw [show p = (symmetricWitness n).map m from rfl,
      natDegree_map_eq_of_injective castInt_injective, symmetricWitness_natDegree]]
  rw [show p.eval (m z) = m ((symmetricWitness n).eval z) by rw [show p = _ from rfl, eval_map, eval₂_hom]]

def worstStart (t : ℕ) (b : R) : R := (-((2 * t - 1 : ℕ) : ℤ) : R) * b

omit [Nontrivial R] [IsAddTorsionFree R] in
private theorem progression_worstStart (t m : ℕ) (b : R) (i : Fin m) :
    progression (fun j : Fin m => j.val) (worstStart t b) b i =
      ((-((2 * t - 1 : ℕ) : ℤ) + (i.val : ℤ) : ℤ) : R) * b := by
  simp [progression, worstStart, add_mul]

theorem regular_step_collision (t : ℕ) (ht : 1 ≤ t) (b : R) (hb : b ∈ nonZeroDivisors R) :
    ∃ f g : R[X], f.support.card = t ∧ g.support.card = t ∧ f ≠ g ∧
      f - g = scaledWitness (2 * t - 1) b ∧
      (∀ i : Fin (4 * t - 1),
        f.eval (progression (fun j : Fin (4 * t - 1) => j.val) (worstStart t b) b i) =
        g.eval (progression (fun j : Fin (4 * t - 1) => j.val) (worstStart t b) b i)) ∧
      f.eval (((2 * t : ℕ) : R) * b) ≠ g.eval (((2 * t : ℕ) : R) * b) := by
  let p := scaledWitness (2 * t - 1) b
  have hcard : p.support.card = 2 * t := by
    dsimp [p]
    rw [scaledWitness_support _ _ hb]
    omega
  have hthird : ∃ u : R, u ≠ 0 ∧ u ≠ 1 :=
    ⟨(Int.castRingHom R) 2, fun hh => by
      have he := castInt_injective (hh.trans (map_zero _).symm)
      norm_num at he, fun hh => by
      have he := castInt_injective (hh.trans (map_one _).symm)
      norm_num at he⟩
  obtain ⟨f, g, _, _, hf, hg, hd⟩ :=
    exact_support_difference_of_third p.support t hthird (by omega) p
      (Finset.Subset.refl _) hcard.le
  refine ⟨f, g, hf, hg, ?_, hd.symm, ?_, ?_⟩
  · intro he
    have hp : p = 0 := by rw [hd, he, sub_self]
    simp [hp] at hcard
    omega
  · intro i
    apply sub_eq_zero.mp
    rw [← eval_sub, ← hd, progression_worstStart t _ b i]
    change (scaledWitness (2 * t - 1) b).eval _ = 0
    rw [scaledWitness_eval]
    have hz : (symmetricWitness (2 * t - 1)).eval (shortPrefixPoint t i) = 0 := by
      apply (symmetricWitness_eval_eq_zero_iff _ _).mpr
      have hi := i.isLt
      dsimp [shortPrefixPoint]
      omega
    rw [show (-((2 * t - 1 : ℕ) : ℤ) + (i.val : ℤ)) = shortPrefixPoint t i from rfl, hz]
    simp
  · intro he
    have hz : (symmetricWitness (2 * t - 1)).eval ((2 * t : ℕ) : ℤ) ≠ 0 := by
      intro hz
      have ha := (symmetricWitness_eval_eq_zero_iff _ _).mp hz
      rw [Int.natAbs_natCast] at ha
      omega
    have hzero : p.eval (((2 * t : ℕ) : R) * b) = 0 := by
      rw [hd, eval_sub, he, sub_self]
    have hscaled := scaledWitness_eval (2 * t - 1) b ((2 * t : ℕ) : ℤ)
    rw [Int.cast_natCast, hzero] at hscaled
    have hreg := mem_nonZeroDivisors_iff_right.mp (pow_mem hb (2 * (2 * t - 1) + 1))
    have hc := hreg _ (by rw [mul_comm]; exact hscaled.symm)
    exact hz ((castInt_injective (R := R)) (hc.trans (map_zero (Int.castRingHom R)).symm))

theorem regular_step_prefix_not_determining (t m : ℕ) (ht : 1 ≤ t) (hm : m < 4 * t)
    (b : R) (hb : b ∈ nonZeroDivisors R) :
    ¬ DeterminesUnboundedSparse (progression (fun i : Fin m => i.val) (worstStart t b) b) t := by
  intro h
  obtain ⟨f, g, hf, hg, hne, _, hobs, _⟩ := regular_step_collision t ht b hb
  apply hne
  refine h f g hf.le hg.le ?_
  intro i
  have hi : i.val < 4 * t - 1 := by have := i.isLt; omega
  exact hobs ⟨i.val, hi⟩

end GrenetPaper
