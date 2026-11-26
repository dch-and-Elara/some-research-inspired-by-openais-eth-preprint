import RootProgram

namespace FourthPaperReview
open RootSeparation RootSeparation.Entry S11 GraphCutMoments

variable {V O : Type*} [Fintype V] [DecidableEq V] [CommRing O]
variable (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)

-- All assignments to the child oracle generate the same root visits.
theorem callbacks_have_identical_visits (σ : V → Bool) (K : ℕ)
    (c₁ c₂ : NativeChild E O) :
    runEvents E reg σ K c₁ = runEvents E reg σ K c₂ := by
  classical
  by_cases h : bigRoot (n (V := V))
  · simp [runEvents, h, sourceTrace_eq_slots]
  · simp [runEvents, h]

-- Operand values never enter the numerical reported bit charge.
theorem operand_values_do_not_enter_charge (σ : V → Bool) (K : ℕ)
    (c : NativeChild E O) (x y : Slot → ℕ) (extra : ℕ) :
    runBitWork E reg σ K c x y extra =
      ((runEvents E reg σ K c).map (fun slot => nativePrecision E slot.center)).sum + extra := by
  simp [runBitWork, accumulatorBitWork, addWord_count, nativePrecision]

-- A lower bound that mentions the actual list of root visits only.
theorem exponential_root_visits (simple : Simple E) (σ : V → Bool) (K : ℕ)
    (child : NativeChild E O) (hn : max (2^131071) K < n (V := V)) :
    (2 : ℝ) ^ ((n (V := V) : ℝ) / (2 * Real.sqrt (Real.logb 2 (n (V := V))))) ≤
      ((runEvents E reg σ K child).length : ℝ) := by
  have hN : bigRoot (n (V := V)) := (le_max_left _ _).trans_lt hn
  have hK : K < size E := ((le_max_right _ _).trans_lt hn).trans_le (by unfold size; omega)
  rw [runEvents_active E simple reg σ K child hN hK, sourceTrace_eq_slots]
  let G := chosenPacking E reg hN
  obtain ⟨_,hc,hpack⟩ := chosenPacking_spec E reg hN
  have hm : 0 < rootM E := by
    rw [show rootM E = 10 * n (V := V) from wire_count E reg]
    have h := bigRoot_n hN
    omega
  obtain ⟨hd, hslots⟩ := odd_root_lower (p := initialPrecision (V := V)) G rfl
    (degreeEnvelope (size E) : ℚ) hc hpack hm (root_certified E reg hN).1
    (root_parameters (size E)).1 rfl
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (exponent_real E reg (bigRoot_n hN) hd)).trans (by
      rw [Real.rpow_natCast]
      exact_mod_cast hslots)

#print axioms callbacks_have_identical_visits
#print axioms operand_values_do_not_enter_charge
#print axioms exponential_root_visits
end FourthPaperReview