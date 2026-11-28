import J4R43LiteralOutsideGreedy
import J4R43LiteralOutsidePhysicalSupply

/-! The selected edges are the output of the literal local-score
derandomizer. Quantitative guards use only the original graph, real
cell census, and finite source schedule. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open P11FullPacking J6R10Repack IndependentThinning
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5500000

variable {E A B G : Type} [Fintype E] [Fintype G] [LinearOrder G]
variable {a : ℕ} {N : Network E A B} (P : PhysicalPacking N a G) (pin : E)

def deterministic_source_marks : Eligible N pin→Bool :=
  deterministicMarks (block N pin) (realColour P pin)

theorem actual_marks_mean_margin (degree : ℕ)
    (dr : ∀ u : A,Nat.card {e : E//N.row e=u}≤degree)
    (dc : ∀ u : B,Nat.card {e : E//N.col e=u}≤degree)
    (margin : ℚ) (margin_nonneg : 0≤margin)
    (large : 4*(Nat.card E:ℚ)*((2*degree-1)*(2*degree-1):ℕ)≤margin^2)
    (c : Cell (Fin a) G) :
    |(Nat.card (RetainedAt P pin (deterministic_source_marks P pin) c):ℚ) -
      meanAt (block N pin) (realColour P pin) c|≤margin := by
  let D := 2*degree-1
  let B := block N pin
  let lab := realColour P pin
  let marks := deterministic_source_marks P pin
  let ω : Outcome (Eligible N pin) := fun e=>(marks e,true)
  have pos : 0<markProbability ω := by
    rw [upside_mass]
    unfold conditionalMass
    exact Finset.prod_pos (fun _ _=>by norm_num [coinAt])
  have score := deterministic_variance_bound B lab D (block_contains N pin)
    (block_symmetric N pin) (literal_block_count N degree dr dc pin)
  have largeE : Fintype.card (Eligible N pin)≤Nat.card E := by
    rw [←Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have bound : rawScore B lab marks≤margin^2 := by
    refine score.trans ((show 4*(Fintype.card (Eligible N pin):ℚ)*(D*D:ℕ)≤
        4*(Nat.card E:ℚ)*(D*D:ℕ) by gcongr).trans large)
  have count : rawCount B lab c marks=countAt B lab c ω := by
    unfold rawCount countAt
    refine Finset.sum_congr rfl fun e _=>?_
    rw [real_count_for_supported_marks B ω pos e]
    by_cases fit : ∀ f∈B e,marks f=decide (f=e) <;>
      simp [rawIndicator,prescribe,required,ω,fit]
  have finite : (rawCount B lab c marks-meanAt B lab c)^2≤rawScore B lab marks :=
    Finset.single_le_sum (fun k _=>sq_nonneg (rawCount B lab k marks-meanAt B lab k))
      (Finset.mem_univ c)
  have h := finite.trans bound
  rw [count,actual_count_is_real_natural P pin ω pos c,←sq_abs] at h
  exact (sq_le_sq₀ (abs_nonneg _) margin_nonneg).mp h

def deterministic_original_matching_supply (h degree : ℕ) (copies : 0<P.copies)
    (dr : ∀ u : A,Nat.card {e : E//N.row e=u}≤degree)
    (dc : ∀ u : B,Nat.card {e : E//N.col e=u}≤degree)
    (margin : ℚ) (margin_nonneg : 0≤margin)
    (large : 4*(Nat.card E:ℚ)*((2*degree-1)*(2*degree-1):ℕ)≤margin^2)
    (census : ∀ c : Cell (Fin a) G,
      ((2*h*P.copies:ℕ):ℚ)+margin≤(Nat.card (EligibleAt P pin c):ℚ)*(1/2:ℚ)^(2*degree-1)) :
    BandSupply P h pin := by
  let marks := deterministic_source_marks P pin
  have hquota (c : Cell (Fin a) G) :
      2*h*P.copies≤Nat.card (RetainedAt P pin marks c) := by
    have q := (census c).trans (mean_in_actual_cell P pin c (2*degree-1)
      (literal_block_count N degree dr dc pin))
    have t := (abs_le.mp (actual_marks_mean_margin P pin degree dr dc margin margin_nonneg large c)).1
    have b : ((2*h*P.copies:ℕ):ℚ)≤(Nat.card (RetainedAt P pin marks c):ℚ) := by
      change -margin≤(Nat.card (RetainedAt P pin marks c):ℚ)-_ at t
      linarith
    exact_mod_cast b
  exact actual_marking_band_supply N pin P h copies marks
    (fun c=>(hquota c).trans (retained_fits_input_fiber P pin marks c))

/-- Size of the actual dense schedule of conditional moment addresses. -/
theorem actual_derandomizer_visit_bound (hcopy : 0<P.copies) :
    Nat.card (Eligible N pin×Bool×
      ((Cell (Fin a) G×Eligible N pin×Eligible N pin)⊕(Cell (Fin a) G×Eligible N pin)))≤
    2*Nat.card E*(3*Nat.card E)*((Nat.card E)^2+Nat.card E) := by
  have he : Fintype.card (Eligible N pin)≤Nat.card E := by
    rw [←Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hc : Fintype.card (Cell (Fin a) G)≤3*Nat.card E := by
    rw [←Nat.card_eq_fintype_card]
    have hp : 0<P.copies*2^a := by positivity
    exact (Nat.le_mul_of_pos_right _ hp).trans P.paddedBudget
  rw [greedy_exact_visit_count]
  gcongr

#print axioms deterministic_source_marks
#print axioms actual_marks_mean_margin
#print axioms deterministic_original_matching_supply
#print axioms actual_derandomizer_visit_bound
end
end J4R43LiteralOutside

