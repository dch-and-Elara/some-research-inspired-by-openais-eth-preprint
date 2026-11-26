import S6Cells
import S6Packing
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Sum

namespace Section6

open Finset
open scoped BigOperators
set_option linter.unusedSectionVars false

noncomputable section

variable {A I H V : Type*} [Fintype A] [LinearOrder A] [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H] [Fintype V] [DecidableEq V]

def swapInt (tag u : A × A) : ℤ :=
  if u = tag then (if tag.1 ≤ tag.2 then 1 else -1)
  else if u = tag.swap then 1 else 0

def walshInt (t u : WordCell I A) : ℤ := ∏ i, swapInt (t i) (u i)

lemma walshInt_cast (t u : WordCell I A) : (walshInt t u : ℚ) = walsh t u := by
  unfold walshInt walsh
  push_cast
  apply prod_congr rfl
  intro i _
  unfold swapInt swapEntry
  split_ifs <;> norm_num

lemma walshInt_abs (t u : WordCell I A) : |walshInt t u| ≤ 1 := by
  rw [walshInt, abs_prod]
  apply prod_le_one
  · exact fun _ _ => abs_nonneg _
  · intro i _
    unfold swapInt
    split_ifs <;> norm_num

def chosenBit (P : Placement V H I A) (i : I) (g : A) (x : V → Bool)
    (h : H) (u : WordCell I A) : ℤ :=
  match P.owner (h,u) with
  | none => 0
  | some v => if P.first v i = g ∧ x v = true then 1 else 0

lemma chosenBit_abs (P : Placement V H I A) (i : I) (g : A) (x : V → Bool) (h : H)
    (u : WordCell I A) : |chosenBit P i g x h u| ≤ 1 := by
  unfold chosenBit
  cases P.owner (h,u) <;> simp
  split_ifs <;> norm_num

def summaryInt (P : Placement V H I A) (window : Finset ℕ) (i : I) (x : V → Bool)
    (g : A) (row : H × Exceptional I A window) : ℤ :=
  ∑ u, walshInt row.2.val u * chosenBit P i g x row.1 u

lemma summaryInt_eq_actual (P : Placement V H I A) (window : Finset ℕ) (i : I) (x : V → Bool)
    (g : A) (row : H × Exceptional I A window) :
    (summaryInt P window i x g row : ℚ) = actualSummary P window i x g row := by
  classical
  unfold actualSummary actualMatrix occurrences Matrix.mulVec dotProduct summaryInt
  simp only [Int.cast_sum, Int.cast_mul, walshInt_cast, sum_filter, sum_mul]
  rw [sum_comm]
  have he (s : H × WordCell I A) :
      (∑ v, (if P.owner s = some v then blockWalsh row.1 row.2.val s else 0) *
        (if P.first v i = g then BooleanMeasurement.bit ℚ (x v) else 0)) =
        blockWalsh row.1 row.2.val s * (chosenBit P i g x s.1 s.2 : ℚ) := by
    cases h : P.owner s with
    | none => simp [chosenBit, h, Prod.mk.eta]
    | some v =>
      simp only [Option.some.injEq, ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
      have hp : P.owner (s.1,s.2) = some v := by simpa using h
      rw [chosenBit, hp]
      by_cases hh : P.first v i = g <;> cases hx : x v <;> simp [hh, hx, BooleanMeasurement.bit]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp only [blockWalsh, ite_mul, zero_mul, sum_ite_irrel, sum_const_zero, Finset.sum_ite_eq', mem_univ, if_true]

lemma summaryInt_abs (P : Placement V H I A) (window : Finset ℕ) (i : I) (x : V → Bool)
    (g : A) (row : H × Exceptional I A window) :
    |summaryInt P window i x g row| ≤ (cubeSize I A : ℤ) := by
  rw [summaryInt]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _u : WordCell I A, (1 : ℤ) := by
      apply sum_le_sum
      intro u _
      rw [abs_mul]
      exact mul_le_one₀ (walshInt_abs _ _) (abs_nonneg _) (chosenBit_abs ..)
    _ = _ := by simp [cubeSize]

abbrev GridCoord (D : ℕ) := {z : ℤ // z ∈ Icc (-(D : ℤ)) (D : ℤ)}

lemma gridCoord_card (D : ℕ) : Fintype.card (GridCoord D) = 2*D+1 := by
  rw [Fintype.card_coe, Int.card_Icc]
  omega

/-- Every attainable node tuple embeds into the source's integer grid. -/
theorem actual_grid_bound (P : Placement V H I A) (window : Finset ℕ) (i : I) :
    (Set.range (actualSummary P window i)).ncard ≤
      (2 * cubeSize I A + 1) ^ Fintype.card (A × (H × Exceptional I A window)) := by
  classical
  let Y := Set.range (actualSummary P window i)
  letI : Fintype Y := Fintype.ofFinite _
  let make (y : Y) (k : A × (H × Exceptional I A window)) : GridCoord (cubeSize I A) :=
    ⟨summaryInt P window i (y.property.choose) k.1 k.2,
      mem_Icc.mpr (abs_le.mp (summaryInt_abs P window i _ _ _))⟩
  have hinj : Function.Injective make := by
    intro a b hab
    apply Subtype.ext
    funext g row
    have heq := congrArg (fun f => (f (g,row)).val) hab
    change summaryInt P window i (a.property.choose) g row =
      summaryInt P window i (b.property.choose) g row at heq
    have cast := congrArg (fun z : ℤ => (z : ℚ)) heq
    dsimp only at cast
    rw [summaryInt_eq_actual, summaryInt_eq_actual] at cast
    rw [a.property.choose_spec, b.property.choose_spec] at cast
    exact cast
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  simpa only [Fintype.card_fun, gridCoord_card] using Fintype.card_le_of_injective make hinj

def taylorCount (n q : ℕ) : ℕ :=
  ∑ j ∈ (range (n + 1)).filter (· ≤ q), 2 ^ j * n.choose j

/-- Upstream finite-difference-cost, evaluated on the actual Taylor count. -/
theorem taylor_generating_upper (n q : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    η ^ q * (taylorCount n q : ℝ) ≤ (1+2*η)^n := by
  rw [taylorCount, Nat.cast_sum, mul_sum]
  have h (j : ℕ) (hj : j ∈ (range (n+1)).filter (· ≤ q)) :
      η^q * ((2^j * n.choose j : ℕ) : ℝ) ≤ (2*η)^j * (n.choose j : ℝ) := by
    push_cast
    rw [mul_pow]
    have hp := pow_le_pow_of_le_one hη.le hη1 (mem_filter.mp hj).2
    have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ (2 : ℝ)^j * (n.choose j : ℝ) by positivity)
    linarith only [hmul]
  apply (sum_le_sum h).trans
  apply (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => by positivity)).trans
  calc
    _ = (2*η+1)^n := by rw [add_pow]; simp
    _ ≤ _ := by rw [add_comm]

/-- The exact literal three-layer tally is at most the source's finite upper
bound when a concrete layout supplies the row and group budgets. -/
theorem literal_scan_upper {G : Type*} [Fintype G]
    (Q n r q D rows maxGroup : ℕ) (sizes : G → ℕ)
    (hg : Fintype.card G = r) (hb : ∀ g, sizes g ≤ maxGroup) :
    2 * Q * taylorCount n q * (2*D+1)^rows * (∑ g, 2 ^ sizes g) ≤
      scanBound Q r (taylorCount n q) D rows maxGroup := by
  have hsum : ∑ g, 2 ^ sizes g ≤ r * 2 ^ maxGroup := by
    calc
      _ ≤ ∑ _g : G, 2 ^ maxGroup := sum_le_sum fun g _ => Nat.pow_le_pow_right (by decide) (hb g)
      _ = _ := by simp [hg]
  unfold scanBound
  exact (Nat.mul_le_mul_left _ hsum).trans_eq (by ring)

#print axioms actual_grid_bound
#print axioms taylor_generating_upper
#print axioms literal_scan_upper

end
end Section6




