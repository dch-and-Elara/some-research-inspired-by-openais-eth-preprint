import J7SeatCertificate
import J7R13Score

/-! Retain the joint deviation score of the very labels whose endpoint matching and seating are constructed. -/
open scoped BigOperators Classical
namespace J7R13
open J7SourceLabels J7SourceConditioning J7FullWordCells J7FullWordAssembly
open P11FullPacking J7SeatSource J7SeatMatching J7SeatPacking J7SeatQuota J7SeatCertificate
noncomputable section
set_option maxHeartbeats 6500000

local instance (priority := 100000) : DecidableEq Slot :=
  fun _ _ => Classical.propDecidable _

local instance (priority := 100000) {P R C : Type*} : DecidableEq (Block P R C) :=
  fun _ _ => Classical.propDecidable _

variable {A Pair Row Col W : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W]
variable {t b : ℕ}

/-- J7.3.1 with finite explicit slack: the actual shared/independent
whole-word law supplies a seating and a single common nonpin matching.
No matching or prearranged word layout is a theorem hypothesis. -/
theorem selected_and_seated_scored
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
    ∃ z : State A (Fin t → A) Pair Row Col,
      JointScore row col z ≤ 32 * (Fintype.card (Wire Pair W) : ℚ) ∧
      ∃ j : Wire Pair W ↪ Physical (t+1) b A,
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
  obtain ⟨z,hz,_,hscore,hdev⟩ := full_supported_selection h row col row_cap clone_cap col_cap reference ref
  change JointScore row col z ≤ 32*(Fintype.card (Wire Pair W):ℚ) at hscore
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
        linarith only [hu,hpc]
      · rw [if_neg hd] at hu
        linarith only [hu]
    refine endMargin.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have he := nonpin_count_as_difference row col z d

    rw [Equiv.apply_symm_apply] at he
    change allCenter A Pair W t - ρ ≤ _ at hl
    rw [he]
    linarith only [hl, hu']
  obtain ⟨j,hs,hf,hR,hC,hp⟩ := source_quota row col z hz capacity B δ hδ devMark degree hMargin
  exact ⟨z,hscore,j,hz,hs,hf,hR,hC,hp⟩

#print axioms selected_and_seated_scored

end
end J7R13