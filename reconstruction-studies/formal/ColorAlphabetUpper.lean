import ColorAlphabetLocal
import Mathlib.Tactic.NormNum

open scoped BigOperators Polynomial

namespace Reconstruction.ColorAlphabet

noncomputable section

variable {n : ℕ} {even : Bool}

private abbrev P (n : ℕ) (even : Bool) := Letters n even × Letters n even

private def roundIndex (j : Round n) : Fin (2*n+1) := ⟨j.val, j.val_lt⟩

private theorem roundIndex_eq (j : Round n) (i : Fin (2*n+1)) :
    roundIndex j = i ↔ j = (i.val : Round n) := by
  have hv : ((i.val : ℕ) : Round n).val = i.val := ZMod.val_natCast_of_lt i.isLt
  constructor
  · intro h
    exact ZMod.val_injective _ ((congrArg Fin.val h).trans hv.symm)
  · intro h
    exact Fin.ext ((congrArg ZMod.val h).trans hv)

private theorem zero_color_iff (u : P n even) : localColor u = 0 ↔ u.1 = u.2 := by
  by_cases h : u.1 = u.2
  · simp [localColor, h]
  · simp only [localColor, h, if_false, iff_false]
    split_ifs with hl
    · intro e
      have hv := congrArg ZMod.val e
      rw [leftColor_val, ZMod.val_zero] at hv
      omega
    · intro e
      have hv := congrArg ZMod.val e
      rw [rightColor_val, ZMod.val_zero] at hv
      omega

private theorem left_fiber (u : P n even) (i : Fin (2*n+1)) :
    localColor u = leftColor i ↔
      letterIndex u.1 < letterIndex u.2 ∧ edgeRound u.1 u.2 = (i.val : Round n) := by
  by_cases h : u.1 = u.2
  · simp only [localColor, h, if_true, lt_self_iff_false, false_and, iff_false]
    intro e
    have hv := congrArg ZMod.val e
    rw [ZMod.val_zero, leftColor_val] at hv
    omega
  · let j := roundIndex (edgeRound u.1 u.2)
    by_cases hl : letterIndex u.1 < letterIndex u.2
    · simp only [localColor, h, if_false, hl, if_true, true_and, ← roundIndex_eq]
      change leftColor j = leftColor i ↔ j = i
      exact ⟨fun he => by
        have hv := congrArg ZMod.val he
        rw [leftColor_val, leftColor_val] at hv
        exact Fin.ext (by omega), congrArg leftColor⟩
    · simp only [localColor, h, if_false, hl, false_and, iff_false]
      change rightColor j ≠ leftColor i
      intro e
      have hv := congrArg ZMod.val e
      rw [rightColor_val, leftColor_val] at hv
      have := j.isLt
      omega

private theorem right_fiber (u : P n even) (i : Fin (2*n+1)) :
    localColor u = rightColor i ↔
      letterIndex u.2 < letterIndex u.1 ∧ edgeRound u.1 u.2 = (i.val : Round n) := by
  by_cases h : u.1 = u.2
  · simp only [localColor, h, if_true, lt_self_iff_false, false_and, iff_false]
    intro e
    have hv := congrArg ZMod.val e
    rw [ZMod.val_zero, rightColor_val] at hv
    omega
  · let j := roundIndex (edgeRound u.1 u.2)
    by_cases hl : letterIndex u.1 < letterIndex u.2
    · have hrev : ¬ letterIndex u.2 < letterIndex u.1 := Nat.not_lt_of_ge hl.le
      simp only [localColor, h, if_false, hl, hrev, if_true, false_and, iff_false]
      change leftColor j ≠ rightColor i
      intro e
      have hv := congrArg ZMod.val e
      rw [leftColor_val, rightColor_val] at hv
      have := i.isLt
      omega
    · have hne : letterIndex u.1 ≠ letterIndex u.2 := fun e => h (letterIndex_injective e)
      have hrev : letterIndex u.2 < letterIndex u.1 := by omega
      simp only [localColor, h, if_false, hl, hrev, true_and, ← roundIndex_eq]
      change rightColor j = rightColor i ↔ j = i
      exact ⟨fun he => by
        have hv := congrArg ZMod.val he
        rw [rightColor_val, rightColor_val] at hv
        exact Fin.ext (by omega), congrArg rightColor⟩

/-- The color-zero class consists of the column sums. Every other color is
one orientation of one round and has the common matching size. -/
theorem localColor_card (g : Colors (2*n+1)) :
    Fintype.card {p : P n even // localColor p = g} =
      (n + if even then 1 else 0) + if g = 0 then n+1 else 0 := by
  classical
  by_cases h : g = 0
  · subst g
    let e : {p : P n even // localColor p = 0} ≃ Letters n even :=
      { toFun := fun p => p.val.1
        invFun := fun a => ⟨(a,a), (zero_color_iff _).mpr rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl ((zero_color_iff _).mp p.property))
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, letters_card]
    simp only [if_true]
    omega
  · rw [if_neg h]
    rcases nonzero_color_boundary g h with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · let e : {p : P n even // localColor p = leftColor i} ≃
          Edges n even (i.val : Round n) :=
        { toFun := fun p => ⟨p.val, (left_fiber _ _).mp p.property⟩
          invFun := fun p => ⟨p.val, (left_fiber _ _).mpr p.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e, edges_card, Nat.add_zero]
    · let e : {p : P n even // localColor p = rightColor i} ≃
          Edges n even (i.val : Round n) :=
        { toFun := fun p => ⟨p.val.swap, ((right_fiber _ _).mp p.property).1,
            (edgeRound_symm _ _).trans ((right_fiber _ _).mp p.property).2⟩
          invFun := fun p => ⟨p.val.swap, (right_fiber _ _).mpr ⟨p.property.1,
            (edgeRound_symm _ _).trans p.property.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e, edges_card, Nat.add_zero]

def alphabetSize (n : ℕ) (even : Bool) : ℕ := 2*n+1 + if even then 1 else 0

def roundEncoder (F : Type*) [Field F] (θ : F) (n : ℕ) (even : Bool) (q : ℕ) :
    Matrix (ColorRows q (@localColor n even) (InInterval 1))
      (Word (fun _ : Fin q => Letters n even)) F :=
  tensorRows (localEntry θ) q localColor (InInterval 1)

theorem roundEncoder_recovers {F : Type*} [Field F] (θ : F) (h0 : θ ≠ 0) (h1 : θ ≠ 1)
    (n : ℕ) (even : Bool) (q : ℕ) : Recovers (roundEncoder F θ n even q) :=
  tensorRows_recovers _ _ _ _ (local_expands θ h1) (local_decodes θ h0)

theorem roundEncoder_rows (n : ℕ) (even : Bool) (q : ℕ) :
    Fintype.card (ColorRows q (@localColor n even) (InInterval 1)) =
      (2*n+1) * ((alphabetSize n even ^ (2*q) - (n+1)^q) / (2*(2*n+1)+1)) := by
  have hN : Fintype.card (P n even) = alphabetSize n even ^ 2 := by
    rw [Fintype.card_prod, letters_card, pow_two]
    rfl
  have hN' : Fintype.card (P n even) = (2*(2*n+1)+1)*(n + if even then 1 else 0)+(n+1) := by
    rw [hN, alphabetSize]
    cases even <;> simp <;> ring
  rw [color_rows_card localColor _ _ _ (by omega) hN' localColor_card _
    (zero_not_mem_one_interval _) q, one_interval_card, hN, ← pow_mul]

private theorem entry_ternary (u v : P n even) :
    localEntry (-1 : ℚ) u v = -1 ∨ localEntry (-1 : ℚ) u v = 0 ∨ localEntry (-1 : ℚ) u v = 1 := by
  classical
  unfold localEntry
  split_ifs with he hcol hlt
  all_goals try norm_num
  all_goals
    have hswap : u ≠ u.swap := fun h => he (congrArg Prod.fst h)
    by_cases h1 : u = v <;> by_cases h2 : u.swap = v
    · exact (hswap (h1.trans h2.symm)).elim
    · unfold delta; rw [if_pos h1, if_neg h2]; norm_num
    · unfold delta; rw [if_neg h1, if_pos h2]; norm_num
    · unfold delta; rw [if_neg h1, if_neg h2]; norm_num

theorem roundEncoder_ternary (n : ℕ) (even : Bool) (q : ℕ)
    (i : ColorRows q (@localColor n even) (InInterval 1))
    (v : Word (fun _ : Fin q => Letters n even)) :
    roundEncoder ℚ (-1) n even q i v = -1 ∨ roundEncoder ℚ (-1) n even q i v = 0 ∨
      roundEncoder ℚ (-1) n even q i v = 1 := by
  unfold roundEncoder tensorRows
  apply Finset.prod_induction _ (fun x : ℚ => x = -1 ∨ x = 0 ∨ x = 1)
  · intro a b ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> norm_num [ha, hb]
  · exact Or.inr (Or.inr rfl)
  · exact fun t _ => entry_ternary _ _

end

end Reconstruction.ColorAlphabet
