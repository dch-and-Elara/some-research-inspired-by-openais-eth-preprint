import BareissSolverCore

/-!
# The common-minor invariant for pivoted elimination

The augmented right-hand side is column `none`. Row and column selections
are ordered. An order-`j` minor at depth `k` is an order-`k+j` minor of the
original integer augmented matrix divided by the same nonzero order-`k`
minor. No determinants are computed by the solver.
-/

open scoped BigOperators

namespace Reconstruction.BareissSolver

abbrev IntegerAugment (m n : ℕ) := Matrix (Fin m) (Option (Fin n)) ℤ

def augmented {m n : ℕ} (A : Coefficients m n) (b : Column m) : Matrix (Fin m) (Option (Fin n)) ℚ :=
  Matrix.of (fun i j => j.elim (b i) (A i))

@[simp] theorem augmented_none {m n : ℕ} (A : Coefficients m n) (b : Column m) (i : Fin m) :
    augmented A b i none = b i := rfl

@[simp] theorem augmented_some {m n : ℕ} (A : Coefficients m n) (b : Column m) (i : Fin m) (j : Fin n) :
    augmented A b i (some j) = A i j := rfl

def integerCoefficients {m n : ℕ} (Z : IntegerAugment m n) : Coefficients m n :=
  denseMatrix (Matrix.of (fun i j => (Z i (some j):ℚ)))

def integerRhs {m n : ℕ} (Z : IntegerAugment m n) : Column m :=
  denseColumn (fun i => (Z i none:ℚ))

@[simp] theorem integerCoefficients_apply {m n : ℕ} (Z : IntegerAugment m n) (i : Fin m) (j : Fin n) :
    integerCoefficients Z i j = Z i (some j) := by simp [integerCoefficients]

@[simp] theorem integerRhs_apply {m n : ℕ} (Z : IntegerAugment m n) (i : Fin m) :
    integerRhs Z i = Z i none := by simp [integerRhs]

theorem augmented_integer {m n : ℕ} (Z : IntegerAugment m n) :
    augmented (integerCoefficients Z) (integerRhs Z) = Z.map (Int.castRingHom ℚ) := by
  ext i j
  cases j <;> simp

/-- In the square bordered matrix, eliminating column zero multiplies the
determinant of the trailing Schur complement by the pivot. -/
theorem det_of_first_pivot {k : ℕ} (B : Matrix (Fin (k+1)) (Fin (k+1)) ℚ)
    (h : B 0 0 ≠ 0) :
    B.det = B 0 0 * (Matrix.of (fun (u v : Fin k) =>
      B u.succ v.succ - B u.succ 0 / B 0 0 * B 0 v.succ)).det := by
  classical
  let E : Matrix (Fin (k+1)) (Fin (k+1)) ℚ := Matrix.of
    (Fin.cases (fun j => if j = 0 then 1 else 0)
      (fun u j => if j = 0 then -(B u.succ 0 / B 0 0) else if j = u.succ then 1 else 0))
  have hEsub : E.submatrix Fin.succ Fin.succ = 1 := by
    ext u v
    simp [E, Matrix.one_apply, Fin.succ_inj, eq_comm]
  have hE : E.det = 1 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [E, Fin.succAbove_zero, hEsub]
  have htop (v : Fin (k+1)) : (E * B) 0 v = B 0 v := by
    simp [E, Matrix.mul_apply]
  have htail (u : Fin k) (v : Fin (k+1)) : (E * B) u.succ v =
      B u.succ v - B u.succ 0 / B 0 0 * B 0 v := by
    simp [E, Matrix.mul_apply, Fin.sum_univ_succ, Fin.succ_inj, ite_mul, sub_eq_add_neg, add_comm]
  have hzero (u : Fin k) : (E * B) u.succ 0 = 0 := by
    rw [htail, div_mul_cancel₀ _ h, sub_self]
  have hsub : (E * B).submatrix Fin.succ Fin.succ = Matrix.of (fun u v =>
      B u.succ v.succ - B u.succ 0 / B 0 0 * B 0 v.succ) := by
    ext u v
    exact htail u v.succ
  have hh := Matrix.det_succ_column_zero (E * B)
  rw [Fin.sum_univ_succ] at hh
  simp only [hzero, htop, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, hsub,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at hh
  rwa [Matrix.det_mul, hE, one_mul] at hh

theorem augmented_step {m n : ℕ} (A : Coefficients (m+1) (n+1)) (b : Column (m+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (u : Fin m) (v : Option (Fin n)) :
    augmented (stepMatrix A i j) (stepRhs A b i j) u v =
      augmented A b (i.succAbove u) (v.map j.succAbove) -
        A (i.succAbove u) j / A i j * augmented A b i (v.map j.succAbove) := by
  cases v <;> simp [multiplier]

theorem det_bordered_step {m n k : ℕ} (A : Coefficients (m+1) (n+1)) (b : Column (m+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (h : A i j ≠ 0)
    (rs : Fin k → Fin m) (cs : Fin k → Option (Fin n)) :
    ((augmented A b).submatrix (Fin.cons i (i.succAbove ∘ rs))
      (Fin.cons (some j) (Option.map j.succAbove ∘ cs))).det =
      A i j * ((augmented (stepMatrix A i j) (stepRhs A b i j)).submatrix rs cs).det := by
  let B := (augmented A b).submatrix (Fin.cons i (i.succAbove ∘ rs))
    (Fin.cons (some j) (Option.map j.succAbove ∘ cs))
  have hp : B 0 0 = A i j := by simp [B]
  rw [show ((augmented A b).submatrix (Fin.cons i (i.succAbove ∘ rs))
    (Fin.cons (some j) (Option.map j.succAbove ∘ cs))).det = B.det from rfl,
    det_of_first_pivot B (hp ▸ h), hp]
  congr 2
  ext u v
  simpa [B, hp] using (augmented_step A b i j (rs u) (cs v)).symm

/-- An ordered determinant of the designated size. Repeated labels give a
zero determinant and obey the same minor bounds. -/
def HasMinor {m n : ℕ} (Z : IntegerAugment m n) (k : ℕ) (z : ℤ) : Prop :=
  ∃ (rs : Fin k → Fin m) (cs : Fin k → Option (Fin n)), (Z.submatrix rs cs).det = z

theorem HasMinor.cast_det {m n k : ℕ} (Z : IntegerAugment m n)
    (rs : Fin k → Fin m) (cs : Fin k → Option (Fin n)) :
    ((Z.submatrix rs cs).det:ℚ) = ((Z.map (Int.castRingHom ℚ)).submatrix rs cs).det :=
  (Int.castRingHom ℚ).map_det (Z.submatrix rs cs)

/-- `d` is a single common denominator for all residual minor orders. -/
structure MinorFrame {m₀ n₀ m n : ℕ} (Z : IntegerAugment m₀ n₀) (depth : ℕ) (d : ℤ)
    (A : Coefficients m n) (b : Column m) : Prop where
  denominator_ne : d ≠ 0
  denominator_minor : HasMinor Z depth d
  minor : ∀ (k : ℕ) (rs : Fin k → Fin m) (cs : Fin k → Option (Fin n)),
    ∃ v : ℤ, HasMinor Z (depth+k) v ∧
      (v:ℚ) = (d:ℚ) * ((augmented A b).submatrix rs cs).det

theorem MinorFrame.initial {m n : ℕ} (Z : IntegerAugment m n) :
    MinorFrame Z 0 1 (integerCoefficients Z) (integerRhs Z) := by
  refine ⟨one_ne_zero, ⟨Fin.elim0, Fin.elim0, by simp⟩, ?_⟩
  intro k rs cs
  refine ⟨(Z.submatrix rs cs).det, ?_, ?_⟩
  · simpa only [zero_add] using (show HasMinor Z k (Z.submatrix rs cs).det from ⟨rs,cs,rfl⟩)
  · rw [HasMinor.cast_det, augmented_integer, Int.cast_one, one_mul]

theorem MinorFrame.entry {m₀ n₀ m n depth : ℕ} {Z : IntegerAugment m₀ n₀} {d : ℤ}
    {A : Coefficients m n} {b : Column m} (F : MinorFrame Z depth d A b)
    (i : Fin m) (j : Option (Fin n)) :
    ∃ v : ℤ, HasMinor Z (depth+1) v ∧ (v:ℚ) = (d:ℚ) * augmented A b i j := by
  obtain ⟨v, hv, he⟩ := F.minor 1 (fun _ => i) (fun _ => j)
  exact ⟨v,hv,by simpa only [Matrix.det_fin_one, Matrix.submatrix_apply] using he⟩

theorem MinorFrame.step {m₀ n₀ m n depth : ℕ} {Z : IntegerAugment m₀ n₀} {d p : ℤ}
    {A : Coefficients (m+1) (n+1)} {b : Column (m+1)} (F : MinorFrame Z depth d A b)
    {i : Fin (m+1)} {j : Fin (n+1)} (hp : A i j ≠ 0)
    (hminor : HasMinor Z (depth+1) p) (hvalue : (p:ℚ) = (d:ℚ)*A i j) :
    MinorFrame Z (depth+1) p (stepMatrix A i j) (stepRhs A b i j) := by
  refine ⟨?_, hminor, ?_⟩
  · intro hz
    rw [hz, Int.cast_zero] at hvalue
    exact (mul_ne_zero (by exact_mod_cast F.denominator_ne) hp) hvalue.symm
  · intro k rs cs
    obtain ⟨v, hv, he⟩ := F.minor (k+1) (Fin.cons i (i.succAbove ∘ rs))
      (Fin.cons (some j) (Option.map j.succAbove ∘ cs))
    refine ⟨v, by simpa only [Nat.add_right_comm depth 1 k] using hv, ?_⟩
    rw [he, det_bordered_step A b i j hp, hvalue, mul_assoc]

/-- Every prefix of the actual deterministic pivot path. The dimensions of
the current state are tracked by the index types. -/
inductive PivotPath {m₀ n₀ : ℕ} (Z : IntegerAugment m₀ n₀) :
    {m n : ℕ} → ℕ → Coefficients m n → Column m → Prop
  | initial : PivotPath Z 0 (integerCoefficients Z) (integerRhs Z)
  | step {m n k : ℕ} {A : Coefficients (m+1) (n+1)} {b : Column (m+1)}
      {i : Fin (m+1)} {j : Fin (n+1)} :
      PivotPath Z k A b → firstPivot A = some (i,j) →
        PivotPath Z (k+1) (stepMatrix A i j) (stepRhs A b i j)

theorem PivotPath.minorFrame {m₀ n₀ m n k : ℕ} {Z : IntegerAugment m₀ n₀}
    {A : Coefficients m n} {b : Column m} (H : PivotPath Z k A b) :
    ∃ d : ℤ, MinorFrame Z k d A b := by
  induction H with
  | initial => exact ⟨1, MinorFrame.initial Z⟩
  | @step m n k A b i j _ hp ih =>
    obtain ⟨d, F⟩ := ih
    obtain ⟨p, hm, he⟩ := F.entry i (some j)
    exact ⟨p, F.step (firstPivot_ne_zero hp) hm he⟩

theorem PivotPath.dimensions {m₀ n₀ m n k : ℕ} {Z : IntegerAugment m₀ n₀}
    {A : Coefficients m n} {b : Column m} (H : PivotPath Z k A b) : k+m = m₀ ∧ k+n = n₀ := by
  induction H with
  | initial => simp
  | step _ _ ih => omega

end Reconstruction.BareissSolver
