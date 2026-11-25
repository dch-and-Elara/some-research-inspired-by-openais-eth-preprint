import BareissSolverInteger

open scoped BigOperators

namespace Reconstruction.BareissSolver

structure ValidResult {m₀ n₀ m n : ℕ} (Z : IntegerAugment m₀ n₀) (depth : ℕ) (d : ℤ)
    (A : Coefficients m n) (b : Column m) (s : ScaledSolution n) : Prop where
  nonzero : s.denominator ≠ 0
  solves : Solves A b s.rational
  basis : ∃ (k : ℕ) (rs : Fin k ↪ Fin m) (cs : Fin k ↪ Fin n),
    (d:ℚ)*(A.submatrix rs cs).det = s.denominator ∧
    HasMinor Z (depth+k) s.denominator ∧
    ∀ j, j ∉ Set.range cs → s.rational j = 0

theorem ValidResult.minors {m₀ n₀ m n depth : ℕ} {Z : IntegerAugment m₀ n₀} {d : ℤ}
    {A : Coefficients m n} {b : Column m} {s : ScaledSolution n}
    (F : MinorFrame Z depth d A b) (H : ValidResult Z depth d A b s) :
    ∃ k ≤ min m n, HasMinor Z (depth+k) s.denominator ∧
      ∀ j, s.numerator j = 0 ∨ HasMinor Z (depth+k) (s.numerator j) := by
  obtain ⟨k,rs,cs,hd,hD,hzero⟩ := H.basis
  have hr : k ≤ m := by simpa using Fintype.card_le_of_embedding rs
  have hc : k ≤ n := by simpa using Fintype.card_le_of_embedding cs
  have hD0 : (s.denominator:ℚ) ≠ 0 := by exact_mod_cast H.nonzero
  refine ⟨k,le_min hr hc,hD,?_⟩
  intro j
  have hv : (s.numerator j:ℚ) = (s.denominator:ℚ)*s.rational j := by
    rw [ScaledSolution.rational_apply, mul_comm, div_mul_cancel₀ _ hD0]
  by_cases hj : j ∈ Set.range cs
  · obtain ⟨u,rfl⟩ := hj
    obtain ⟨a,ha,he⟩ := F.cramer rs cs H.solves hzero hd u
    exact Or.inr ((show a = s.numerator (cs u) by exact_mod_cast he.trans hv.symm) ▸ ha)
  · left
    rw [hzero j hj, mul_zero] at hv
    exact_mod_cast hv

private theorem validZero {m₀ n₀ m n depth : ℕ} {Z : IntegerAugment m₀ n₀} {d : ℤ}
    {A : Coefficients m n} {b : Column m} (F : MinorFrame Z depth d A b)
    (h : Solves A b 0) : ValidResult Z depth d A b ⟨d,0⟩ := by
  have he : (⟨d,0⟩ : ScaledSolution n).rational = 0 := by ext; simp
  refine ⟨F.denominator_ne,he.symm ▸ h,0,⟨Fin.elim0,fun i => i.elim0⟩,
    ⟨Fin.elim0,fun i => i.elim0⟩,?_,?_,?_⟩
  · simp
  · simpa using F.denominator_minor
  · simp

theorem backwardStep_spec {m₀ n₀ m n depth : ℕ} {Z : IntegerAugment m₀ n₀} {d : ℤ}
    {A : Coefficients (m+1) (n+1)} {b : Column (m+1)} {M : IntegerAugment (m+1) (n+1)}
    (F : MinorFrame Z depth d A b) (E : Represents M d A b) {i : Fin (m+1)} {j : Fin (n+1)}
    (h : A i j ≠ 0) {s : ScaledSolution n}
    (H : ValidResult Z (depth+1) (M i (some j)) (stepMatrix A i j) (stepRhs A b i j) s) :
    M i (some j) ∣ backwardDividend M i j s ∧
      (backwardStep M i j s).rational = restore A b i j s.rational ∧
      ValidResult Z depth d A b (backwardStep M i j s) := by
  let y := restore A b i j s.rational
  obtain ⟨k,rs,cs,hdet,hD,hzero⟩ := H.basis
  have hdet' : (d:ℚ)*(A.submatrix (insertPick i rs) (insertPick j cs)).det = s.denominator := by
    rw [det_insertPick A i j h rs cs, ← mul_assoc, ← augmented_some A b i j, ← E]
    exact hdet
  have hy : Solves A b y := solves_restore h H.solves
  have hyzero := restore_supported A b i j cs s.rational hzero
  obtain ⟨a, _, ha⟩ := F.cramer (insertPick i rs) (insertPick j cs) hy hyzero hdet' 0
  rw [insertPick_zero] at ha
  have hD0 : (s.denominator:ℚ) ≠ 0 := by exact_mod_cast H.nonzero
  have hNum (u : Fin n) : (s.numerator u:ℚ) = (s.denominator:ℚ)*s.rational u := by
    rw [ScaledSolution.rational_apply, mul_comm, div_mul_cancel₀ _ hD0]
  have hp : M i (some j) ≠ 0 := by
    intro hz
    have hh := E i (some j)
    rw [hz, Int.cast_zero, augmented_some] at hh
    exact (mul_ne_zero (by exact_mod_cast F.denominator_ne) h) hh.symm
  have hrow : A i j*y j + (∑ v, A i (j.succAbove v)*s.rational v) = b i := by
    have hh := hy i
    rw [Fin.sum_univ_succAbove (fun v => A i v * y v) j] at hh
    simpa only [y, restore_other] using hh
  have hDividend : backwardDividend M i j s = M i (some j)*a := by
    apply Int.cast_injective (α := ℚ)
    calc
      (backwardDividend M i j s:ℚ) =
          ((s.denominator:ℚ)*(d:ℚ))*b i -
            ∑ v, ((d:ℚ)*A i (j.succAbove v))*((s.denominator:ℚ)*s.rational v) := by
        rw [backwardDividend_sum]
        have hCoeff (v : Fin n) : (M i (some (j.succAbove v)):ℚ) = (d:ℚ)*A i (j.succAbove v) :=
          E i (some (j.succAbove v))
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, E i none, hCoeff, augmented_none, hNum, mul_assoc]
      _ = ((s.denominator:ℚ)*(d:ℚ))*(b i - ∑ v, A i (j.succAbove v)*s.rational v) := by
        rw [mul_sub, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ((s.denominator:ℚ)*(d:ℚ))*(A i j * y j) := by rw [← hrow]; ring
      _ = ((M i (some j)*a:ℤ):ℚ) := by rw [Int.cast_mul, E, augmented_some, ha]; ring
  have he : (backwardStep M i j s).rational = y := by
    funext u
    induction u using Fin.succAboveCases j with
    | x =>
      simp only [ScaledSolution.rational_apply, backwardStep, denseIntColumn_apply,
        Fin.insertNth_apply_same, hDividend, Int.mul_ediv_cancel_left _ hp, ha, mul_comm (s.denominator:ℚ)]
      exact mul_div_cancel_right₀ _ hD0
    | p u => simp [backwardStep, y]
  refine ⟨⟨a,hDividend⟩,he,⟨H.nonzero,he.symm ▸ hy,k+1,insertPick i rs,insertPick j cs,hdet',?_,?_⟩⟩
  · simpa only [Nat.add_right_comm depth 1 k] using hD
  · simpa only [he] using hyzero

private theorem integerZero_refines {m₀ n₀ m n depth : ℕ} {Z : IntegerAugment m₀ n₀} {d : ℤ}
    {A : Coefficients m n} {b : Column m} {M : IntegerAugment m n}
    (F : MinorFrame Z depth d A b) (E : Represents M d A b) (hA : ∀ i j, A i j = 0) :
    (integerZero M d).map ScaledSolution.rational = (zeroSolution b : Option (Column n)) ∧
      ∀ s, integerZero M d = some s → ValidResult Z depth d A b s := by
  have hd : (d:ℚ) ≠ 0 := by exact_mod_cast F.denominator_ne
  have h (i : Fin m) : M i none = 0 ↔ b i = 0 := by
    have he := E i none
    rw [augmented_none] at he
    constructor
    · intro h
      rw [h, Int.cast_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left hd
    · intro h
      rw [h, mul_zero] at he
      exact_mod_cast he
  by_cases hb : ∀ i, b i = 0
  · have he : (⟨d,0⟩ : ScaledSolution n).rational = 0 := by ext; simp
    have hv : ValidResult Z depth d A b ⟨d,0⟩ := validZero F (by simp [Solves, hA, hb])
    simp [integerZero, zeroAnswer, zeroSolution, h, hb, he]
    exact hv
  · simp [integerZero, zeroAnswer, zeroSolution, h, hb]

/-- The integer implementation refines rational Gaussian elimination. On
success, its common denominator is a minor, and every nonzero numerator is
also a minor of the cleared input. -/
theorem runInt_correct {m₀ n₀ : ℕ} {Z : IntegerAugment m₀ n₀} (m n depth : ℕ) (d : ℤ)
    (A : Coefficients m n) (b : Column m) (M : IntegerAugment m n)
    (F : MinorFrame Z depth d A b) (E : Represents M d A b) :
    (runInt m n M d).result.map ScaledSolution.rational = solveCore m n A b ∧
      ∀ s, (runInt m n M d).result = some s → ValidResult Z depth d A b s := by
  induction m generalizing n depth d with
  | zero =>
    have he : (⟨d,0⟩ : ScaledSolution n).rational = 0 := by ext; simp
    have hv : ValidResult Z depth d A b ⟨d,0⟩ := validZero F (by simp [Solves])
    exact ⟨by simp [runInt, solveCore, he], fun _ e => (Option.some.inj e) ▸ hv⟩
  | succ m ih =>
    cases n with
    | zero => exact integerZero_refines F E (fun _ j => j.elim0)
    | succ n =>
      have hq := integerPivot_eq F.denominator_ne E
      rw [runInt, solveCore, ← hq]
      dsimp only [integerPivot]
      cases hp : (pivotScan M).found with
      | none => exact integerZero_refines F E (firstPivot_none (hq.symm.trans hp))
      | some p =>
        obtain ⟨i,j⟩ := p
        dsimp only
        have ha := firstPivot_ne_zero (hq.symm.trans hp)
        obtain ⟨F', E', _⟩ := forwardStep_spec F E ha
        have H := ih n (depth+1) (M i (some j)) (stepMatrix A i j) (stepRhs A b i j)
          (forwardStep M d i j) F' E'
        cases hs : (runInt m n (forwardStep M d i j) (M i (some j))).result with
        | none =>
          have hh := H.1
          rw [hs, Option.map_none] at hh
          simp [← hh]
        | some s =>
          have hh := H.1
          rw [hs, Option.map_some] at hh
          obtain ⟨_, hr, hv⟩ := backwardStep_spec F E ha (H.2 s hs)
          refine ⟨by simp [← hh, hr], ?_⟩
          intro s' he
          simp only [Option.map_some, Option.some.injEq] at he
          exact he ▸ hv

end Reconstruction.BareissSolver
