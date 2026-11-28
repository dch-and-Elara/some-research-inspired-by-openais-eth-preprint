import J7PrintedParams
import J7ToJ8Source
import J7ToJ8Degree

/-! # Substitute the actual four-clone J7 print parameters in the native J8 bridge. -/
open scoped BigOperators Classical

namespace J7PrintedParams

open J7SourceLabels J7FullWordCells J7FullWordAssembly J7SeatSource
open J7SeatPacking J7SeatCertificate J7SeatMatching J7SeatRounded P11FullPacking
open J7ToJ8Incidence J7ToJ8Layout J7ToJ8Source J7ToJ8Degree

noncomputable section
set_option maxHeartbeats 1600000

def printedD (t : ℕ) : ℕ := (64:ℕ)^(2*(t+1))
def printedL (t : ℕ) : ℕ := 2^(t+1)

theorem printedD_pos (t : ℕ) : 0 < printedD t := by unfold printedD; positivity

theorem printedD_is_L12 (t : ℕ) : printedD t = printedL t ^ 12 := by
  unfold printedD printedL
  rw [show (64:ℕ)=2^6 by decide, ← pow_mul, ← pow_mul]
  congr 1
  omega

theorem printed_denom (A : Type*) [Fintype A] (hA : Fintype.card A = 64) (t : ℕ) :
    denom A (Fin t → A) = (printedD t : ℚ) := by
  rw [denom_coordinates, hA, printedD, Nat.cast_pow, Nat.cast_ofNat]

variable {A Pair Row Col W : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t : ℕ}

/-- Finite J7/J8 for the four-clone physical incidence counts. The only
remaining numerical inputs are the source's printed packing inequalities
and an explicit large-L threshold. The real matching degree is derived,
not an external witness. -/
theorem printed_endpoints
    (hA : Fintype.card A = 64) (N Δ : ℕ)
    (hN : Fintype.card (Pin Pair) = N) (hM : Fintype.card (Wire Pair W) = 24*N)
    (hL : 131072 ≤ printedL t)
    (packing1 : 2*(printedD t)^2*Δ ≤ 24*N)
    (packing2 : printedL t * printedD t ≤ 24*N) (packing3 : 2*printedL t ≤ Δ)
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_two : ∀ r, Nat.card {w : W // row w = r} = 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3)
    (reference : State A (Fin t → A) Pair Row Col) (ref : Seed A (Fin t → A)) :
    ∃ z : State A (Fin t → A) Pair Row Col,
      let b' := ceilCopies (2^(t+1)) (realMaximum (wordLabel row col z))
      (b' : ℚ)*(printedL t : ℚ) ≤ 3*mu N (printedD t) ∧
      ∃ j : Wire Pair W ↪ Physical (t+1) b' A,
      ∃ preserve : ∀ w, physicalCell (balancedMask (t+1) b') (j w) = wordLabel row col z w,
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      let layout := physicalLayout row col row_two z j preserve
      Nonempty (J8Physical.EndpointSeating layout) ∧
      (∀ p (x : J8Physical.Wire (Subdivision Pair Row)),
        ¬ J8Physical.Shift layout x (J8Physical.pinWire layout p)) ∧
      (∀ x y, J8Physical.Shift layout x y → layout.rowLabel x.1 = J8Physical.actualColLabel layout y) ∧
      (∀ p, (J8Physical.targets layout (J8Physical.pinWire layout p)).Nonempty) := by
  classical
  let d := printedD t
  let l := printedL t
  have hm := margin N d l Δ (printedD_pos t) hL packing1 packing2 packing3
  have hAtwo : 2 ≤ Fintype.card A := by rw [hA]; decide
  have hrow : ∀ r, (Finset.univ.filter fun w : W => row w = r).card ≤ 2 := by
    intro r
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, row_two r]
  have hcent : allCenter A Pair W t = mu N d := by
    unfold allCenter mu
    rw [hM, printed_denom A hA, Nat.cast_mul, Nat.cast_ofNat]
  have hpin : pinCap A Pair t = pinMeanUpper N d := by
    unfold pinCap pinMeanUpper
    rw [hA, hN, printed_denom A hA]
    norm_num [d]
  have hnonpin : (Nat.card {w : Wire Pair W // nonpin col w} : ℚ) ≤ 24*(N:ℚ) := by
    have hn := Fintype.card_subtype_le (fun w : Wire Pair W => nonpin col w)
    rw [hM] at hn
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast hn
  have hword : 32*(Fintype.card (Wire Pair W) : ℚ) ≤ (rho N d)^2 := by
    rw [hM]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hm.word
  have hmark : (Nat.card {w : Wire Pair W // nonpin col w} : ℚ)*5^2 ≤ (delta N d)^2 :=
    (mul_le_mul_of_nonneg_right hnonpin (by positivity)).trans hm.mark
  have hcap : allCenter A Pair W t + rho N d ≤ (bUpper N d l : ℚ)*2^(t+1) := by
    rw [hcent]
    simpa only [l, printedL, Nat.cast_pow, Nat.cast_ofNat] using hm.capacity
  have hend : 2*(bUpper N d l : ℚ)+delta N d ≤
      (allCenter A Pair W t - pinCap A Pair t - 2*rho N d)*(1/2:ℚ)^5 := by
    rw [hcent,hpin]
    exact hm.endpointMargin
  obtain ⟨z,hb,j,hpres,hfull,hendpts,hnop,hchild,htarget⟩ :=
    compile_selected_source hAtwo row col row_two hrow clone_cap col_cap reference ref
      5 (rho N d) (delta N d) hm.rho_nonneg hm.delta_nonneg hword hcap
      (physical_degree_le_five row col row_two clone_cap col_cap) hmark hend
  have hbq : (ceilCopies (2^(t+1)) (realMaximum (wordLabel row col z)) : ℚ) ≤ bUpper N d l := by
    exact_mod_cast hb
  have hp := (mul_le_mul_of_nonneg_right hbq (show 0 ≤ (l:ℚ) by positivity)).trans hm.padded
  exact ⟨z,hp,j,hpres,hfull,hendpts,hnop,hchild,htarget⟩

#print axioms printedD_is_L12
#print axioms printed_denom
#print axioms printed_endpoints

end
end J7PrintedParams
