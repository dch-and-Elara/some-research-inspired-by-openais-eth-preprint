import J7SeatMatching
import J7SeatSource

/-! # Quantitative finite criterion for seating all actual packet endpoints. -/
open scoped BigOperators Classical

namespace J7SeatQuota
open J7SourceConditioning J7SeatMatching J7SeatSource

noncomputable section
set_option maxHeartbeats 1300000

theorem deviation_lower (x y r : ℚ) (hr : 0 ≤ r) (h : (x-y)^2 ≤ r^2) : y-r ≤ x := by
  by_contra! hbad
  have hp : 0 < (y-x-r)*(y-x+r) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- The exact finite analogue of `Omega(H_pad)`: if the half-power
survival mean clears quota by the RMS error, a single matching meets
every quota, not just every cell separately. -/
theorem finite_quota {E U V C : Type*} [Fintype E] [Fintype C]
    (r : E → U) (c : E → V) (label : E → C) (B quota : ℕ) (err : ℚ)
    (degree : ∀ e, (nearby r c e).card ≤ B)
    (herr : 0 ≤ err) (hv : (Fintype.card E : ℚ)*(B:ℚ)^2 ≤ err^2)
    (margin : ∀ i, (quota : ℚ) + err ≤
      (Nat.card {e // label e = i} : ℚ) * (1/2 : ℚ)^B) :
    ∃ g : Set E, g.InjOn r ∧ g.InjOn c ∧
      ∀ i, quota ≤ Nat.card {e : {e // label e = i} // e.val ∈ g} := by
  classical
  obtain ⟨z,hr,hc,hz⟩ := choose_matching r c label B degree
  refine ⟨{e | chosen r c z e}, hr,hc,?_⟩
  intro i
  have hs (e : E) :
      (if label e = i then (1/2:ℚ)^B else 0) ≤
        (if label e = i then (1/2:ℚ)^(nearby r c e).card else 0) := by
    by_cases he : label e = i
    · rw [if_pos he,if_pos he]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (degree e)
    · simp [he]
  have hmean : (Nat.card {e // label e = i} : ℚ) * (1/2:ℚ)^B ≤
      ∑ e : E, if label e = i then (1/2:ℚ)^(nearby r c e).card else 0 := by
    rw [cast_card_eq_indicator, Finset.sum_mul]
    exact Finset.sum_le_sum fun e _ => by simpa only [indicator, ite_mul, one_mul, zero_mul] using hs e
  have hright := deviation_lower _ _ err herr ((hz i).trans hv)
  have hcard : (Nat.card {e : {e // label e = i} // e.val ∈ {e | chosen r c z e}} : ℚ) =
      ∑ e : E, indicator (markedCell r c label e z) (some i) := by
    rw [cast_card_matching]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold markedCell indicator
    by_cases hh : chosen r c z e <;> simp [hh]
  rw [← hcard] at hright
  have last : (quota : ℚ) ≤ (Nat.card {e : {e // label e = i} // e.val ∈ {e | chosen r c z e}} : ℚ) := by
    linarith [margin i]
  exact_mod_cast last

open J7SourceLabels J7FullWordCells J7FullWordAssembly P11FullPacking J7SeatPacking

variable {A Pair Row Col W : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W]
variable {t b : ℕ}

omit [AddCommGroup A] [Fintype Row] [Fintype Col] in
/-- Execute the exact finite argument after fixing the original J7 word
law. The hypotheses are finite slack, not a supplied matching. -/
theorem source_quota (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin t → A) Pair Row Col) (hz : ∀ d, 0 < weight d (z d))
    (cap : ∀ c, Nat.card {w // wordLabel row col z w = c} ≤ b*2^(t+1))
    (B : ℕ) (err : ℚ) (herr : 0 ≤ err)
    (hv : (Nat.card {w // nonpin col w} : ℚ)*(B:ℚ)^2 ≤ err^2)
    (degree : ∀ (w : {w // nonpin col w}),
      (nearby (fun p => rowNode row p.val) (fun p => colNode col p.val) w).card ≤ B)
    (margin : ∀ c, (2*b : ℚ) + err ≤
      (Nat.card {w : {w // nonpin col w} // wordLabel row col z w.val = c} : ℚ) * (1/2 : ℚ)^B) :
    ∃ j : Wire Pair W ↪ Physical (t+1) b A,
      (∀ w, physicalCell (balancedMask (t+1) b) (j w) = wordLabel row col z w) ∧
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      (Set.InjOn (rowNode row) {w | isEnd (j w)}) ∧
      (Set.InjOn (colNode col) {w | isEnd (j w)}) ∧
      (∀ p : Pin Pair, ¬isEnd (j (pinEmbed Pair W p)) ∧
        ((physicalCell (balancedMask (t+1) b) (j (pinEmbed Pair W p))) 0).1 ≠
          ((physicalCell (balancedMask (t+1) b) (j (pinEmbed Pair W p))) 0).2) := by
  classical
  rw [Nat.card_eq_fintype_card] at hv
  obtain ⟨g,hr,hc,hq⟩ := finite_quota
    (fun p : {w // nonpin col w} => rowNode row p.val)
    (fun p => colNode col p.val) (fun p => wordLabel row col z p.val)
    B (2*b) err degree herr hv (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using margin)
  let matched : Set (Wire Pair W) := fun w => ∃ h : nonpin col w, (⟨w,h⟩ : {w // nonpin col w}) ∈ g
  have hmR : matched.InjOn (rowNode row) := by
    rintro x ⟨hx,hx'⟩ y ⟨hy,hy'⟩ he
    exact congrArg Subtype.val (hr hx' hy' he)
  have hmC : matched.InjOn (colNode col) := by
    rintro x ⟨hx,hx'⟩ y ⟨hy,hy'⟩ he
    exact congrArg Subtype.val (hc hx' hy' he)
  have hmP : ∀ w ∈ matched, nonpin col w := fun w hw => hw.choose
  have hmQ (i : Cell (Fin (t+1)) A) :
      2*b ≤ Nat.card {w : {w // wordLabel row col z w = i} // w.val ∈ matched} := by
    let e : {w : {w : {w // nonpin col w} // wordLabel row col z w.val = i} // w.val ∈ g} ↪
      {w : {w // wordLabel row col z w = i} // w.val ∈ matched} :=
      ⟨fun w => ⟨⟨w.val.val.val,w.val.prop⟩,⟨w.val.val.prop,w.prop⟩⟩, by
        intro x y he
        have hh := congrArg (fun w : {w : {w // wordLabel row col z w = i} // w.val ∈ matched} =>
          w.val.val) he
        exact Subtype.ext (Subtype.ext (Subtype.ext hh))⟩
    exact (hq i).trans (Nat.card_le_card_of_injective e e.injective)
  obtain ⟨j,hj,_,hf,hR,hC,hp⟩ := seat_source row col z hz matched hmR hmC hmP cap hmQ
  exact ⟨j,hj,hf,hR,hC,hp⟩

#print axioms finite_quota
#print axioms source_quota

end
end J7SeatQuota
