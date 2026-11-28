import J7SeatQuota

/-! # A single J7 certificate starts with the full-word sampling law. -/

open scoped BigOperators Classical

namespace J7SeatCertificate
open J7SourceLabels J7SourceConditioning J7FullWordCells J7FullWordAssembly
open P11FullPacking J7SeatSource J7SeatMatching J7SeatPacking J7SeatQuota

noncomputable section
set_option maxHeartbeats 1800000

variable {A Pair Row Col W : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W]
variable {t b : ℕ}

omit [LinearOrder A] [AddCommGroup A] [Fintype A] [Fintype W] [Fintype Col] in
theorem pin_nonpin_complement (col : W → OrdinaryColumn Pair Col) (w : Wire Pair W) :
    nonpin col w ↔ w ∉ pinWires Pair W := by
  classical
  rcases w with ⟨p,k⟩ | w
  · cases k <;> simp [nonpin,colNode,pinWires,pinEmbed]
  · simp [nonpin,colNode,pinWires,pinEmbed]

def allCenter (A Pair W : Type*) [Fintype A] [Fintype Pair] [Fintype W] (t : ℕ) : ℚ :=
  (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin t → A)

def pinCap (A Pair : Type*) [Fintype A] [Fintype Pair] (t : ℕ) : ℚ :=
  ((Fintype.card A : ℚ) / (Fintype.card A - 1)) *
    ((Fintype.card (Pin Pair) : ℚ) / denom A (Fin t → A))

omit [AddCommGroup A] [Fintype A] [Fintype Row] [Fintype Col] in
theorem nonpin_count_as_difference (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin t → A) Pair Row Col) (d : Word A (Fin t → A) × Word A (Fin t → A)) :
    (Nat.card {w : {w // nonpin col w} // wordLabel row col z w.val = cellChartEq A t d} : ℚ) =
      (∑ w : Wire Pair W, indicator (fullCell row col w z) d) -
      (∑ w ∈ pinWires Pair W, indicator (fullCell row col w z) d) := by
  classical
  let E := Wire Pair W
  let f : E → Word A (Fin t → A) × Word A (Fin t → A) := fun w => fullCell row col w z
  let e : {w : {w // nonpin col w} // wordLabel row col z w.val = cellChartEq A t d} ≃
      {w : {w : E // f w = d} // nonpin col w.val} :=
    ⟨fun w => ⟨⟨w.val.val,(cellChartEq A t).injective w.prop⟩,w.val.prop⟩,
      fun w => ⟨⟨w.val.val,w.prop⟩,congrArg (cellChartEq A t) w.val.prop⟩,
      by rintro ⟨⟨_w,_⟩,_⟩; rfl, by rintro ⟨⟨_w,_⟩,_⟩; rfl⟩
  rw [Nat.card_congr e,cast_card_matching]

  have hfilter : Finset.univ.filter (fun w => w ∈ pinWires Pair W) = pinWires Pair W := by
    ext w; simp
  rw [← hfilter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [pin_nonpin_complement]
  by_cases h : w ∈ pinWires Pair W <;> by_cases hd : f w = d <;> simp [indicator,f,h,hd] at *

/-- J7.3.1 with finite explicit slack: the actual shared/independent
whole-word law supplies a seating and a single common nonpin matching.
No matching or prearranged word layout is a theorem hypothesis. -/
theorem selected_and_seated
    (h : 2 ≤ Fintype.card A)
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_cap : ∀ r, (Finset.univ.filter fun w : W => row w = r).card ≤ 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3)
    (reference : State A (Fin t → A) Pair Row Col) (ref : Seed A (Fin t → A))
    (B : ℕ) (ρ δ : ℚ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (devWord : 32*(Fintype.card (Wire Pair W) : ℚ) ≤ ρ^2)
    (cap : allCenter A Pair W t + ρ ≤ b*(2:ℚ)^(t+1))
    (degree : ∀ (w : {w // nonpin col w}),
      (nearby (fun p => rowNode row p.val) (fun p => colNode col p.val) w).card ≤ B)
    (devMark : (Nat.card {w // nonpin col w} : ℚ)*(B:ℚ)^2 ≤ δ^2)
    (endMargin : (2*b:ℚ)+δ ≤ (allCenter A Pair W t - pinCap A Pair t - 2*ρ)*(1/2:ℚ)^B) :
    ∃ z : State A (Fin t → A) Pair Row Col, ∃ j : Wire Pair W ↪ Physical (t+1) b A,
      (∀ d, 0 < weight d (z d)) ∧
      (∀ w, physicalCell (balancedMask (t+1) b) (j w) = wordLabel row col z w) ∧
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      (Set.InjOn (rowNode row) {w | isEnd (j w)}) ∧
      (Set.InjOn (colNode col) {w | isEnd (j w)}) ∧
      (∀ p : Pin Pair, ¬isEnd (j (pinEmbed Pair W p)) ∧
        ((physicalCell (balancedMask (t+1) b) (j (pinEmbed Pair W p))) 0).1 ≠
          ((physicalCell (balancedMask (t+1) b) (j (pinEmbed Pair W p))) 0).2) := by
  classical
  letI : DecidableEq A := fun _ _ => Classical.propDecidable _
  obtain ⟨z,hz,_,_,hdev⟩ := full_supported_selection h row col row_cap clone_cap col_cap reference ref
  have capacity := capacity_of_deviation row col z ρ hρ cap (fun c => (hdev c).1.trans devWord)
  have hpc : 0 ≤ pinCap A Pair t := by
    have hr : (2:ℚ) ≤ Fintype.card A := by exact_mod_cast h
    have hr' : (0:ℚ) ≤ (Fintype.card A : ℚ) - 1 := by linarith
    unfold pinCap
    exact mul_nonneg (div_nonneg (by positivity) hr') (div_nonneg (by positivity) (by unfold denom; positivity))
  have hMargin (c : Cell (Fin (t+1)) A) : (2*b:ℚ)+δ ≤
      (Nat.card {w : {w // nonpin col w} // wordLabel row col z w.val = c} : ℚ)*(1/2:ℚ)^B := by
    let d := (cellChartEq A t).symm c
    have ht := (hdev d).1.trans devWord
    have hp := (hdev d).2.trans devWord
    have hl := deviation_lower _ _ ρ hρ ht
    have hu := deviation_lower
      (-(∑ w ∈ pinWires Pair W, indicator (fullCell row col w z) d))
      (-(if d.1.1 = d.2.1 then 0 else pinCap A Pair t)) ρ hρ
      (by

        rw [show ∀ (x y : ℚ), (-x - -y)^2 = (x-y)^2 by intros; ring]
        exact hp)
    have hu' : (∑ w ∈ pinWires Pair W, indicator (fullCell row col w z) d) ≤ pinCap A Pair t + ρ := by
      by_cases hd : d.1.1 = d.2.1
      · rw [if_pos hd] at hu
        linarith
      · rw [if_neg hd] at hu
        linarith
    refine endMargin.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have he := nonpin_count_as_difference row col z d

    rw [Equiv.apply_symm_apply] at he
    change allCenter A Pair W t - ρ ≤ _ at hl
    linarith
  obtain ⟨j,hs,hf,hR,hC,hp⟩ := source_quota row col z hz capacity B δ hδ devMark degree hMargin
  exact ⟨z,j,hz,hs,hf,hR,hC,hp⟩

#print axioms pin_nonpin_complement
#print axioms nonpin_count_as_difference
#print axioms selected_and_seated

end
end J7SeatCertificate
