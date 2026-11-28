import ColorAlphabetMatching
import ColorAlphabetCyclic
import ColorAlphabetCount
import Mathlib.Tactic.FieldSimp

open scoped BigOperators

namespace Reconstruction.ColorAlphabet

noncomputable section

variable {n : ℕ} {even : Bool} {F : Type*} [Field F]

private abbrev L (n : ℕ) (even : Bool) := Letters n even
private abbrev P (n : ℕ) (even : Bool) := L n even × L n even

def delta (u v : P n even) : F := if u = v then 1 else 0

/-- Local columns sums on the diagonal and the two orientations of each
off-diagonal edge, with the lower orientation carrying the coefficient theta. -/
def localEntry (θ : F) (u v : P n even) : F :=
  if u.1 = u.2 then
    if v.2 = u.2 then 1 else 0
  else if letterIndex u.1 < letterIndex u.2 then
    delta u v + delta u.swap v
  else
    delta u.swap v + θ * delta u v

def localColor (u : P n even) : Colors (2*n+1) :=
  if u.1 = u.2 then 0 else
    let j : Fin (2*n+1) := ⟨(edgeRound u.1 u.2).val, (edgeRound u.1 u.2).val_lt⟩
    if letterIndex u.1 < letterIndex u.2 then leftColor j else rightColor j

private def evaluate (θ : F) (c : P n even → F) (v : P n even) : F :=
  ∑ j, c j * localEntry θ j v

private def single (u : P n even) (c : F) : P n even → F :=
  fun v => if v = u then c else 0

private theorem evaluate_single (θ c : F) (u v : P n even) :
    evaluate θ (single u c) v = c * localEntry θ u v := by
  simp [evaluate, single, ite_mul]

private theorem evaluate_sub (θ : F) (c d : P n even → F) (v : P n even) :
    evaluate θ (c - d) v = evaluate θ c v - evaluate θ d v := by
  simp [evaluate, sub_mul, Finset.sum_sub_distrib]

private theorem evaluate_sum {J : Type*} (θ : F) (s : Finset J)
    (c : J → P n even → F) (v : P n even) :
    evaluate θ (∑ i ∈ s, c i) v = ∑ i ∈ s, evaluate θ (c i) v := by
  simp only [evaluate, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem evaluate_column (θ : F) (a : L n even) (v : P n even) :
    evaluate θ (single (a,a) 1) v = ∑ x : L n even, delta (x,a) v := by
  rw [evaluate_single, one_mul, localEntry, if_pos rfl]
  rcases v with ⟨b,c⟩
  by_cases h : c = a
  · simp [delta, Prod.mk.injEq, h]
  · simp [delta, Prod.mk.injEq, h, Ne.symm h]

private theorem less_swap_iff {u : P n even} (hu : u.1 ≠ u.2) :
    letterIndex u.2 < letterIndex u.1 ↔ ¬ letterIndex u.1 < letterIndex u.2 := by
  have hx : letterIndex u.1 ≠ letterIndex u.2 := fun h => hu (letterIndex_injective h)
  omega

private theorem offdiag_expands (θ : F) (hθ : θ ≠ 1) (u : P n even) (hu : u.1 ≠ u.2) :
    ∃ c, ∀ v, evaluate θ c v = delta u v := by
  have hθ' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have hswap : u.swap.1 ≠ u.swap.2 := Ne.symm hu
  by_cases hlt : letterIndex u.1 < letterIndex u.2
  · refine ⟨single u (θ / (θ - 1)) - single u.swap (1 / (θ - 1)), ?_⟩
    intro v
    rw [evaluate_sub, evaluate_single, evaluate_single]
    have hnot : ¬ letterIndex u.swap.1 < letterIndex u.swap.2 := Nat.not_lt_of_ge hlt.le
    simp only [localEntry, hu, hswap, if_false, hlt, if_true, hnot, Prod.swap_swap]
    field_simp
    ring
  · refine ⟨single u (1 / (θ - 1)) - single u.swap (1 / (θ - 1)), ?_⟩
    intro v
    rw [evaluate_sub, evaluate_single, evaluate_single]
    have hlt' : letterIndex u.swap.1 < letterIndex u.swap.2 := (less_swap_iff hu).mpr hlt
    simp only [localEntry, hu, hswap, if_false, hlt, if_true, hlt', Prod.swap_swap]
    field_simp
    ring

private theorem solve_by_column (θ : F) (a b : L n even) (c : L n even → P n even → F)
    (v : P n even) (hc : ∀ x ≠ a, evaluate θ (c x) v = delta (x,b) v) :
    evaluate θ (single (b,b) 1 - ∑ x ∈ Finset.univ.erase a, c x) v = delta (a,b) v := by
  rw [evaluate_sub, evaluate_column, evaluate_sum]
  have e : ∑ x ∈ Finset.univ.erase a, evaluate θ (c x) v =
      ∑ x ∈ Finset.univ.erase a, delta (x,b) v :=
    Finset.sum_congr rfl (fun x hx => hc x (Finset.mem_erase.mp hx).1)
  rw [e, ← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  ring

theorem local_expands (θ : F) (hθ : θ ≠ 1) (u : P n even) :
    ∃ c : P n even → F, ∀ v, ∑ j, c j * localEntry θ j v = if u = v then 1 else 0 := by
  classical
  by_cases h : u.1 = u.2
  · rcases u with ⟨a,b⟩
    change a = b at h
    subst a
    have hx (x : L n even) : ∃ c, x ≠ b → ∀ v, evaluate θ c v = delta (x,b) v := by
      by_cases he : x = b
      · exact ⟨0, fun h => (h he).elim⟩
      · obtain ⟨c, hc⟩ := offdiag_expands θ hθ (x,b) he
        exact ⟨c, fun _ => hc⟩
    choose c hc using hx
    exact ⟨_, fun v => solve_by_column θ b b c v (fun x he => hc x he v)⟩
  · exact offdiag_expands θ hθ u h

private theorem interval_shift {k : ℕ} (g c : Colors k) :
    InInterval (1 : Colors k) (c + g) ↔ InInterval (1 - g) c := by
  have h : (c + g) - 1 = c - (1 - g) := by ring
  simp only [InInterval, h]

private theorem edge_visible {s : Colors (2*n+1)} {u : P n even} (hu : u.1 ≠ u.2)
    (h₁ : ¬InInterval s (localColor u)) (h₂ : ¬InInterval s (localColor u.swap)) :
    s = matchingStart ⟨(edgeRound u.1 u.2).val, (edgeRound u.1 u.2).val_lt⟩ := by
  have hne : u.swap.1 ≠ u.swap.2 := Ne.symm hu
  have hs : edgeRound u.swap.1 u.swap.2 = edgeRound u.1 u.2 := edgeRound_symm _ _
  by_cases hlt : letterIndex u.1 < letterIndex u.2
  · have hnot : ¬ letterIndex u.swap.1 < letterIndex u.swap.2 := Nat.not_lt_of_ge hlt.le
    simp only [localColor, hu, hne, hlt, hnot, if_false, if_true, hs] at h₁ h₂
    exact omitted_boundaries_force_start _ s h₁ h₂
  · have hlt' : letterIndex u.swap.1 < letterIndex u.swap.2 := (less_swap_iff hu).mpr hlt
    simp only [localColor, hu, hne, hlt, hlt', if_false, if_true, hs] at h₁ h₂
    exact omitted_boundaries_force_start _ s h₂ h₁

private def LocalDecoder (θ : F) (s : Colors (2*n+1)) (u : P n even)
    (c : P n even → F) : Prop :=
  (∀ k, ¬InInterval s (localColor k) → c k = 0) ∧
    ∀ v, v.1 ≠ u.2 → evaluate θ c v = delta u v

private theorem visible_decodes (θ : F) (hθ : θ ≠ 0) (s : Colors (2*n+1)) (u : P n even)
    (hu : u.1 ≠ u.2) (hw : InInterval s (localColor u) ∨ InInterval s (localColor u.swap)) :
    ∃ c, LocalDecoder θ s u c := by
  classical
  have zeroSwap (v : P n even) (hv : v.1 ≠ u.2) : delta u.swap v = (0 : F) := by
    exact if_neg fun h => hv ((congrArg Prod.fst h).symm)
  have support (a : P n even) (h : InInterval s (localColor a)) (c : F) (k : P n even)
      (hk : ¬ InInterval s (localColor k)) : single a c k = 0 :=
    if_neg (fun e : k = a => hk (by simpa only [e] using h))
  by_cases h : InInterval s (localColor u)
  · by_cases hlt : letterIndex u.1 < letterIndex u.2
    · refine ⟨single u 1, support u h 1, fun v hv => ?_⟩
      rw [evaluate_single, one_mul, localEntry, if_neg hu, if_pos hlt, zeroSwap v hv, add_zero]
    · refine ⟨single u θ⁻¹, support u h θ⁻¹, fun v hv => ?_⟩
      rw [evaluate_single, localEntry, if_neg hu, if_neg hlt, zeroSwap v hv,
        zero_add, ← mul_assoc, inv_mul_cancel₀ hθ, one_mul]
  · have hs := hw.resolve_left h
    refine ⟨single u.swap 1, support u.swap hs 1, fun v hv => ?_⟩
    rw [evaluate_single, one_mul, localEntry, if_neg (show u.swap.1 ≠ u.swap.2 from Ne.symm hu)]
    split_ifs <;> simp [zeroSwap v hv]

theorem local_decodes (θ : F) (hθ : θ ≠ 0) (g : Colors (2*n+1)) (u : P n even) :
    ∃ c : P n even → F,
      (∀ k, ¬ InInterval (1 : Colors (2*n+1)) (localColor k + g) → c k = 0) ∧
      ∀ v, v.1 ≠ u.2 → ∑ k, c k * localEntry θ k v = if u = v then 1 else 0 := by
  classical
  let s := 1 - g
  have solve : ∃ c, LocalDecoder θ s u c := by
    by_cases he : u.1 = u.2
    · refine ⟨0, by simp, ?_⟩
      intro v hv
      simp [evaluate, delta, show u ≠ v from fun h => hv (h ▸ he)]
    · by_cases hvis : InInterval s (localColor u) ∨ InInterval s (localColor u.swap)
      · exact visible_decodes θ hθ s u he hvis
      · push_neg at hvis
        have hs := edge_visible he hvis.1 hvis.2
        let a := u.1
        let b := u.2
        have hz : InInterval s 0 := hs.symm ▸ zero_in_matchingInterval _
        have hothers (x : L n even) : ∃ c, x ≠ a → LocalDecoder θ s (x,b) c := by
          by_cases hx : x = a
          · exact ⟨0, fun h => (h hx).elim⟩
          · by_cases hxb : x = b
            · refine ⟨0, fun _ => ⟨by simp, fun v hv => ?_⟩⟩
              simp [evaluate, delta, show (x,b) ≠ v from fun h => hv (h ▸ hxb)]
            · have hsee : InInterval s (localColor (x,b)) ∨
                  InInterval s (localColor (b,x)) := by
                by_contra! hn
                have hstart := edge_visible hxb hn.1 hn.2
                have hr := matchingStart_injective (hs.symm.trans hstart)
                have hv := congrArg Fin.val hr
                have hm : edgeRound b a = edgeRound b x := by
                  rw [edgeRound_symm b a, edgeRound_symm b x]
                  exact ZMod.val_injective _ hv
                exact hx (edgeRound_unique (Ne.symm he) (Ne.symm hxb) hm).symm
              obtain ⟨c, hc⟩ := visible_decodes θ hθ s (x,b) hxb hsee
              exact ⟨c, fun _ => hc⟩
        choose c hc using hothers
        refine ⟨single (b,b) 1 - ∑ x ∈ Finset.univ.erase a, c x, ?_, ?_⟩
        · intro k hk
          have hne : k ≠ (b,b) := fun h => hk (h.symm ▸ (by simpa [localColor] using hz))
          simp only [Pi.sub_apply, Finset.sum_apply, single, if_neg hne, zero_sub, neg_eq_zero]
          apply Finset.sum_eq_zero
          intro x hx
          exact (hc x (Finset.mem_erase.mp hx).1).1 k hk
        · intro v hv
          exact solve_by_column θ a b c v (fun x hx => (hc x hx).2 v hv)
  obtain ⟨c, hc, hd⟩ := solve
  exact ⟨c, fun k hk => hc k (mt (interval_shift g (localColor k)).mpr hk), hd⟩

end

end Reconstruction.ColorAlphabet
