import ColorAlphabetUpper
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators Polynomial

namespace Reconstruction.ColorAlphabet

noncomputable section

private def relabelWord {q : ℕ} {A B : Type*} (e : A ≃ B) :
    Word (fun _ : Fin q => A) ≃ Word (fun _ : Fin q => B) :=
  Equiv.piCongrRight (fun _ => e.prodCongr e)

private theorem relabel_recovers {q : ℕ} {F I A B : Type*} [Field F] [Fintype I]
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (C : Matrix I (Word (fun _ : Fin q => A)) F)
    (h : Recovers C) : Recovers (C.reindex (Equiv.refl _) (relabelWord e)) := by
  intro u t z hz hs
  let v := (relabelWord e).symm u
  let w (x : Word (fun _ : Fin q => A)) := z (relabelWord e x)
  have hw (i : I) : ∑ x, C i x * w x = 0 := by
    have hh := hz i
    rw [← (relabelWord e).sum_comp] at hh
    simpa [w] using hh
  have hv (x : Word (fun _ : Fin q => A)) (hx : (x t).1 = (v t).2) : w x = 0 := by
    apply hs
    change e (x t).1 = (u t).2
    rw [hx]
    exact congrArg (fun y : Word (fun _ : Fin q => B) => (y t).2)
      ((relabelWord e).apply_symm_apply u)
  have hzero := h v t w hw hv
  change z (relabelWord e ((relabelWord e).symm u)) = 0 at hzero
  rw [Equiv.apply_symm_apply] at hzero
  exact hzero

/-- The rational ternary construction on the physical alphabet Fin r.
The inequality is the finite bound with its positive denominator cleared. -/
theorem ternary_finite_upper (q r : ℕ) (hr : 1 ≤ r) (a : Fin q → ℚ) :
    ∃ (m : ℕ) (C : Matrix (Fin m) (Word (fun _ : Fin q => Fin r)) ℚ)
      (P : Matrix (Word (fun _ : Fin q => Fin r)) (Word (fun _ : Fin q => Fin r)) ℚ[X]),
      FeasibleZero a C P ∧ (∀ i v, C i v = -1 ∨ C i v = 0 ∨ C i v = 1) ∧
      (if r % 2 = 0 then 2*r-1 else 2*r+1) * C.rank ≤
        (if r % 2 = 0 then r-1 else r) *
          (r ^ (2*q) - (if r % 2 = 0 then r/2 else (r+1)/2) ^ q) := by
  classical
  have round (n : ℕ) (even : Bool) :
      ∃ (m : ℕ) (C : Matrix (Fin m) (Word (fun _ : Fin q => Fin (alphabetSize n even))) ℚ)
        (P : Matrix (Word (fun _ : Fin q => Fin (alphabetSize n even)))
          (Word (fun _ : Fin q => Fin (alphabetSize n even))) ℚ[X]),
        FeasibleZero a C P ∧ (∀ i v, C i v = -1 ∨ C i v = 0 ∨ C i v = 1) ∧
        (2*(2*n+1)+1)*C.rank ≤
          (2*n+1) * (alphabetSize n even ^ (2*q) - (n+1)^q) := by
    let C := roundEncoder ℚ (-1) n even q
    let e : Letters n even ≃ Fin (alphabetSize n even) :=
      (Fintype.equivFin _).trans (finCongr (letters_card n even))
    let ei := Fintype.equivFin (ColorRows q (@localColor n even) (InInterval 1))
    let C' := C.reindex (Equiv.refl _) (relabelWord e)
    let D := C'.reindex ei (Equiv.refl _)
    have hrec : Recovers C' :=
      relabel_recovers e C (roundEncoder_recovers (-1 : ℚ) (by norm_num) (by norm_num) n even q)
    have hd : Recovers D := by
      intro u t z hz hs
      exact hrec u t z (fun i => by simpa [D] using hz (ei i)) hs
    obtain ⟨P, hP⟩ := (feasibleZero_exists_iff a D).mpr hd
    refine ⟨_, D, P, hP, fun j v => roundEncoder_ternary _ _ _ _ _, ?_⟩
    have hrank : D.rank ≤ Fintype.card (ColorRows q (@localColor n even) (InInterval 1)) := by
      simpa [D, C', C, Matrix.rank_reindex] using C.rank_le_card_height
    have hrank' := hrank.trans_eq (roundEncoder_rows n even q)
    refine (Nat.mul_le_mul_left _ hrank').trans ?_
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
  by_cases h : r % 2 = 0
  · let n := r/2 - 1
    have he : alphabetSize n true = r := by simp [alphabetSize, n]; omega
    have hk : 2*n+1 = r-1 := by dsimp [n]; omega
    have hp : 2*(2*n+1)+1 = 2*r-1 := by omega
    have hm : n+1 = r/2 := by dsimp [n]; omega
    have H := round n true
    rw [hp, hk, hm, he] at H
    simpa only [h, if_true] using H
  · let n := r/2
    have he : alphabetSize n false = r := by simp [alphabetSize, n]; omega
    have hk : 2*n+1 = r := by dsimp [n]; omega
    have hm : n+1 = (r+1)/2 := by dsimp [n]; omega
    have H := round n false
    rw [hk, hm, he] at H
    simpa only [h, if_false] using H

private theorem round_field {F : Type*} [Field F] (θ : F) (h0 : θ ≠ 0) (h1 : θ ≠ 1)
    (n : ℕ) (even : Bool) (q : ℕ) (a : Fin q → F) :
    ∃ (m : ℕ) (C : Matrix (Fin m) (Word (fun _ : Fin q => Fin (alphabetSize n even))) F)
      (P : Matrix (Word (fun _ : Fin q => Fin (alphabetSize n even)))
        (Word (fun _ : Fin q => Fin (alphabetSize n even))) F[X]),
      FeasibleZero a C P ∧ m =
        (2*n+1) * ((alphabetSize n even ^ (2*q) - (n+1)^q) / (2*(2*n+1)+1)) ∧ C.rank ≤ m := by
  classical
  let C := roundEncoder F θ n even q
  let e : Letters n even ≃ Fin (alphabetSize n even) :=
    (Fintype.equivFin _).trans (finCongr (letters_card n even))
  let ei := Fintype.equivFin (ColorRows q (@localColor n even) (InInterval 1))
  let C' := C.reindex (Equiv.refl _) (relabelWord e)
  let D := C'.reindex ei (Equiv.refl _)
  have hrec : Recovers C' := relabel_recovers e C (roundEncoder_recovers θ h0 h1 n even q)
  have hd : Recovers D := by
    intro u t z hz hs
    exact hrec u t z (fun i => by simpa [D] using hz (ei i)) hs
  obtain ⟨P, hP⟩ := (feasibleZero_exists_iff a D).mpr hd
  exact ⟨_, D, P, hP, roundEncoder_rows n even q, by simpa using D.rank_le_card_height⟩

/-- The binary encoder works with a scalar other than 0 and 1 in place
of the rational encoder's coefficient -1. -/
theorem binary_field_upper {F : Type*} [Field F] (θ : F) (h0 : θ ≠ 0) (h1 : θ ≠ 1)
    (q : ℕ) (a : Fin q → F) :
    ∃ (m : ℕ) (C : Matrix (Fin m) (Word (fun _ : Fin q => Fin 2)) F)
      (P : Matrix (Word (fun _ : Fin q => Fin 2)) (Word (fun _ : Fin q => Fin 2)) F[X]),
      FeasibleZero a C P ∧ m = (4^q-1)/3 ∧ C.rank ≤ (4^q-1)/3 := by
  obtain ⟨m, C, P, hP, hm, hrank⟩ := round_field θ h0 h1 0 true q a
  change m = 1 * ((2^(2*q)-1^q)/3) at hm
  rw [pow_mul, one_pow, one_mul] at hm
  exact ⟨m, C, P, hP, hm, hrank.trans_eq hm⟩

end

end Reconstruction.ColorAlphabet
