
import GuardExpectation
import GuardedPacking

namespace GuardAssembly
open scoped BigOperators
open GuardExpectation GuardedPacking

variable {E I T : Type*} [Fintype E] [DecidableEq E]
  [Fintype (I → Bool)] [DecidableEq (I → Bool)]

omit [Fintype E] [DecidableEq E] [Fintype (I → Bool)] in
theorem multiplicities_agree (label : E → Bool → I → Bool)
    (e : E) (c : I → Bool) :
    portMultiplicity label e c = multiplicity label e c := by
  simp [portMultiplicity, GuardedPacking.multiplicity, Fintype.card_subtype]

omit [DecidableEq E] in
theorem centered_marked {L : ℕ} (a : E → Fin L) (z : Fin L) (d : E → ℕ) :
    centeredLoad (L : ℚ)⁻¹ z (fun e => (d e : ℚ)) a =
      ((∑ e ∈ markedSet a z, d e : ℕ) : ℚ) -
        (∑ e, (d e : ℚ)) * (L : ℚ)⁻¹ := by
  rw [centeredLoad_eq]
  congr 1
  push_cast
  rw [markedSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : a e = z
  · simp [indicator, h]
  · simp [indicator, h]

/-- The P9 marking/deletion/seating chain for both packet endpoints. This
    constructs finite marked whole equalities and their disjoint seat maps,
    using the actual squared-deviation budget; it does not change graph labels. -/
theorem select_and_seat {L : ℕ} (hL : 2 ≤ L)
    (label : E → Bool → I → Bool) (b : ℕ)
    (capacity : ∀ c, ((cellLoad (multiplicity label) Finset.univ c : ℕ) : ℝ) / L ≤ b) :
    ∃ keep : Bool → Finset E,
      Disjoint (keep false) (keep true) ∧
      ∀ s : Bool,
        (∀ c : I → Bool, Nonempty (markedPort label (keep s) c ↪
          {p : (I → Bool) × Fin b // endMask s p.1 = c})) ∧
        (Fintype.card E : ℝ) / L ≤ (keep s).card +
          Real.sqrt (5 * (2 * (Fintype.card E : ℝ)) / L) +
          Real.sqrt ((Fintype.card (I → Bool) : ℝ) *
            (5 * (2 * (Fintype.card E : ℝ)) / L)) := by
  classical
  obtain ⟨a, ha, hpot⟩ := exists_port_marking_by_conditioning hL label
  let m := fun s => markedSet a (signSymbol L hL s)
  let μ := fun c => ((cellLoad (multiplicity label) Finset.univ c : ℕ) : ℝ) / L
  let B : ℝ := 5 * (2 * (Fintype.card E : ℝ)) / L
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have one (s : Bool) :
      ((m s).card - (Fintype.card E : ℝ)/L)^2 +
        (∑ c, ((cellLoad (multiplicity label) (m s) c : ℝ) - μ c)^2) ≤ B := by
    let v := fun t : Bool =>
      (centeredLoad (L : ℚ)⁻¹ (signSymbol L hL t) (fun _ => 1) a)^2 +
        ∑ c, (centeredLoad (L : ℚ)⁻¹ (signSymbol L hL t)
          (fun e => (portMultiplicity label e c : ℚ)) a)^2
    have hv : v s ≤ ∑ t, v t :=
      Finset.single_le_sum (fun t _ => by dsimp [v]; positivity) (Finset.mem_univ s)
    have hr := hv.trans hpot
    have hc0 : centeredLoad (L : ℚ)⁻¹ (signSymbol L hL s) (fun _ => 1) a =
        ((m s).card : ℚ) - (Fintype.card E : ℚ)/L := by
      simpa [m, div_eq_mul_inv] using
        (centered_marked a (signSymbol L hL s) (fun (_ : E) => 1))
    have hc1 (c : I → Bool) :
        centeredLoad (L : ℚ)⁻¹ (signSymbol L hL s)
          (fun e => (portMultiplicity label e c : ℚ)) a =
        (cellLoad (multiplicity label) (m s) c : ℚ) -
          (cellLoad (multiplicity label) Finset.univ c : ℚ)/L := by
      simpa [m, cellLoad, div_eq_mul_inv, multiplicities_agree, Nat.cast_sum] using
        (centered_marked a (signSymbol L hL s) (fun e => portMultiplicity label e c))
    change (centeredLoad _ _ _ a)^2 + ∑ c, (centeredLoad _ _ _ a)^2 ≤ _ at hr
    simp only [hc0, hc1] at hr
    dsimp [μ, B]
    have hr' := (Rat.cast_le (K := ℝ)).mpr hr
    push_cast at hr'
    exact hr'
  have build (s : Bool) : ∃ t : Finset E, t ⊆ m s ∧
      (∀ c : I → Bool, Nonempty (markedPort label t c ↪
        {p : (I → Bool) × Fin b // endMask s p.1 = c})) ∧
      (Fintype.card E : ℝ) / L ≤ t.card + Real.sqrt B +
        Real.sqrt ((Fintype.card (I → Bool) : ℝ) * B) := by
    have h := one s
    have hs : ((m s).card - (Fintype.card E : ℝ)/L)^2 ≤ B :=
      (le_add_of_nonneg_right (by positivity)).trans h
    have hd : (∑ c, ((cellLoad (multiplicity label) (m s) c : ℝ) - μ c)^2) ≤ B :=
      (le_add_of_nonneg_left (sq_nonneg _)).trans h
    have ht : (Fintype.card E : ℝ)/L - (m s).card ≤ Real.sqrt B := by
      by_cases hneg : (Fintype.card E : ℝ)/L - (m s).card ≤ 0
      · exact hneg.trans (Real.sqrt_nonneg _)
      · apply (Real.le_sqrt (le_of_not_ge hneg) hB).mpr
        nlinarith
    exact seat_from_deviations label (m s) b s μ capacity _ _ B hB (by linarith) hd
  choose keep hsub hseat hret using build
  exact ⟨keep, Finset.disjoint_left.mpr (fun e he hf =>
    Finset.disjoint_left.mp ha (hsub false he) (hsub true hf)),
    fun s => ⟨hseat s, hret s⟩⟩

#print axioms select_and_seat
end GuardAssembly

