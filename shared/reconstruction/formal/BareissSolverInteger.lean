import BareissSolverCramer

open scoped BigOperators

namespace Reconstruction.BareissSolver

abbrev IntColumn (n : ℕ) := Fin n → ℤ

def denseIntColumn {n : ℕ} (x : IntColumn n) : IntColumn n :=
  let data := Vector.ofFn x
  fun i => data[i.val]

@[simp] theorem denseIntColumn_apply {n : ℕ} (x : IntColumn n) (i : Fin n) :
    denseIntColumn x i = x i := by simp [denseIntColumn]

def denseAugment {m n : ℕ} (Z : IntegerAugment m n) : IntegerAugment m n :=
  let data := Vector.ofFn (fun i => Vector.ofFn (Fin.cons (Z i none) (fun j => Z i (some j))))
  Matrix.of (fun i j => data[i.val][(j.elim (0 : Fin (n+1)) Fin.succ).val])

@[simp] theorem denseAugment_apply {m n : ℕ} (Z : IntegerAugment m n) (i : Fin m) (j : Option (Fin n)) :
    denseAugment Z i j = Z i j := by cases j <;> simp [denseAugment]

/-- The active integer table stores the numerator matrix at the common
denominator of the active rational system. -/
def Represents {m n : ℕ} (M : IntegerAugment m n) (d : ℤ) (A : Coefficients m n) (b : Column m) : Prop :=
  ∀ i j, (M i j:ℚ) = (d:ℚ)*augmented A b i j

theorem represents_initial {m n : ℕ} (Z : IntegerAugment m n) :
    Represents (denseAugment Z) 1 (integerCoefficients Z) (integerRhs Z) := by
  simp [Represents, augmented_integer]

/-- The two products and subtraction before the exact division. -/
def forwardDividend {m n : ℕ} (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (u : Fin m) (v : Option (Fin n)) : ℤ :=
  M i (some j) * M (i.succAbove u) (v.map j.succAbove) -
    M (i.succAbove u) (some j) * M i (v.map j.succAbove)

def forwardStep {m n : ℕ} (M : IntegerAugment (m+1) (n+1)) (d : ℤ)
    (i : Fin (m+1)) (j : Fin (n+1)) : IntegerAugment m n :=
  denseAugment (Matrix.of (fun u v => forwardDividend M i j u v / d))

theorem forwardStep_spec {m₀ n₀ m n depth : ℕ} {Z : IntegerAugment m₀ n₀}
    {d : ℤ} {A : Coefficients (m+1) (n+1)} {b : Column (m+1)}
    {M : IntegerAugment (m+1) (n+1)} (F : MinorFrame Z depth d A b) (E : Represents M d A b)
    {i : Fin (m+1)} {j : Fin (n+1)} (h : A i j ≠ 0) :
    MinorFrame Z (depth+1) (M i (some j)) (stepMatrix A i j) (stepRhs A b i j) ∧
    Represents (forwardStep M d i j) (M i (some j)) (stepMatrix A i j) (stepRhs A b i j) ∧
    ∀ u v, d ∣ forwardDividend M i j u v ∧
      HasMinor Z (depth+1+1) (forwardStep M d i j u v) := by
  obtain ⟨p, hm, hp⟩ := F.entry i (some j)
  have he : p = M i (some j) := by exact_mod_cast (hp.trans (E i (some j)).symm)
  have F' := F.step h (he ▸ hm) (he ▸ hp)
  have H (u : Fin m) (v : Option (Fin n)) :
      ∃ z : ℤ, HasMinor Z (depth+1+1) z ∧
        (z:ℚ) = (M i (some j):ℚ)*augmented (stepMatrix A i j) (stepRhs A b i j) u v ∧
        forwardDividend M i j u v = d*z := by
    obtain ⟨z, hz, hz'⟩ := F'.entry u v
    refine ⟨z,hz,hz',?_⟩
    have hcast : (forwardDividend M i j u v:ℚ) = ((d*z:ℤ):ℚ) := by
      simp only [forwardDividend, Int.cast_sub, Int.cast_mul, E i (some j),
        E (i.succAbove u) (v.map j.succAbove), E (i.succAbove u) (some j), E i (v.map j.succAbove),
        augmented_some, hz', augmented_step]
      field_simp
    exact_mod_cast hcast
  refine ⟨F', ?_, ?_⟩
  · intro u v
    obtain ⟨z, _, he, hmul⟩ := H u v
    simpa only [forwardStep, denseAugment_apply, Matrix.of_apply, hmul, Int.mul_ediv_cancel_left _ F.denominator_ne] using he
  · intro u v
    obtain ⟨z, hz, _, hmul⟩ := H u v
    exact ⟨⟨z,hmul⟩, by simpa only [forwardStep, denseAugment_apply, Matrix.of_apply, hmul,
      Int.mul_ediv_cancel_left _ F.denominator_ne] using hz⟩

structure ScaledSolution (n : ℕ) where
  denominator : ℤ
  numerator : IntColumn n

def ScaledSolution.rational {n : ℕ} (x : ScaledSolution n) : Column n :=
  denseColumn (fun j => (x.numerator j:ℚ)/(x.denominator:ℚ))

@[simp] theorem ScaledSolution.rational_apply {n : ℕ} (x : ScaledSolution n) (j : Fin n) :
    x.rational j = (x.numerator j:ℚ)/(x.denominator:ℚ) := by simp [ScaledSolution.rational]

def backwardDividend {m n : ℕ} (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) : ℤ :=
  x.denominator * M i none - (List.finRange n).foldl
    (fun s v => s + M i (some (j.succAbove v))*x.numerator v) 0

theorem backwardDividend_sum {m n : ℕ} (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) :
    backwardDividend M i j x = x.denominator * M i none -
      ∑ v, M i (some (j.succAbove v))*x.numerator v := by
  simp [backwardDividend, fold_add_eq_sum, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

def backwardStep {m n : ℕ} (M : IntegerAugment (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : ScaledSolution n) : ScaledSolution (n+1) :=
  ⟨x.denominator, denseIntColumn (Fin.insertNth j (backwardDividend M i j x / M i (some j)) x.numerator)⟩

/-- The labels actually tested by a left-to-right search, including the first hit. -/
structure Scan (α : Type*) where
  found : Option α
  tested : List α

def scanNonzero {α : Type*} (read : α → ℤ) : List α → Scan α
  | [] => ⟨none, []⟩
  | a :: xs =>
    if read a = 0 then
      let tail := scanNonzero read xs
      ⟨tail.found, a :: tail.tested⟩
    else ⟨some a, [a]⟩

theorem scanNonzero_found {α : Type*} (read : α → ℤ) (xs : List α) :
    (scanNonzero read xs).found = xs.find? (fun a => decide (read a ≠ 0)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => by_cases h : read a = 0 <;> simp [scanNonzero, List.find?, h, ih]

theorem scanNonzero_length {α : Type*} (read : α → ℤ) (xs : List α) :
    (scanNonzero read xs).tested.length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => by_cases h : read a = 0 <;> simp [scanNonzero, h, ih]

def pivotScan {m n : ℕ} (M : IntegerAugment m n) : Scan (Fin m × Fin n) :=
  scanNonzero (fun p => M p.1 (some p.2)) (candidates m n)

abbrev integerPivot {m n : ℕ} (M : IntegerAugment m n) := (pivotScan M).found

def rhsScan {m n : ℕ} (M : IntegerAugment m n) : Scan (Fin m) :=
  scanNonzero (fun i => M i none) (List.finRange m)

theorem pivotScan_length {m n : ℕ} (M : IntegerAugment m n) : (pivotScan M).tested.length ≤ m*n := by
  simpa [pivotScan] using scanNonzero_length (fun p => M p.1 (some p.2)) (candidates m n)

theorem rhsScan_length {m n : ℕ} (M : IntegerAugment m n) : (rhsScan M).tested.length ≤ m := by
  simpa [rhsScan] using scanNonzero_length (fun i => M i none) (List.finRange m)

@[simp] theorem rhsScan_none {m n : ℕ} (M : IntegerAugment m n) :
    (rhsScan M).found = none ↔ ∀ i, M i none = 0 := by
  simp [rhsScan, scanNonzero_found, List.find?_eq_none]

theorem integerPivot_eq {m n : ℕ} {M : IntegerAugment m n} {d : ℤ}
    {A : Coefficients m n} {b : Column m} (hd : d ≠ 0) (E : Represents M d A b) :
    integerPivot M = firstPivot A := by
  have hd' : (d:ℚ) ≠ 0 := by exact_mod_cast hd
  have h (p : Fin m × Fin n) : (M p.1 (some p.2) ≠ 0) ↔ A p.1 p.2 ≠ 0 := by
    have he := E p.1 (some p.2)
    rw [augmented_some] at he
    constructor
    · intro hn hz
      apply hn
      have hcast : (M p.1 (some p.2):ℚ) = 0 := he.trans (by rw [hz, mul_zero])
      exact_mod_cast hcast
    · intro hn hz
      apply hn
      apply (mul_eq_zero.mp ?_).resolve_left hd'
      rw [← he, hz, Int.cast_zero]
  unfold integerPivot pivotScan firstPivot
  rw [scanNonzero_found]
  congr 1
  funext p
  by_cases hp : M p.1 (some p.2) ≠ 0
  · simp [hp, (h p).mp hp]
  · have hq : A p.1 p.2 = 0 := not_not.mp (fun hq => hp ((h p).mpr hq))
    simp [hp, hq]

def zeroAnswer {m n : ℕ} (d : ℤ) (scan : Scan (Fin m)) : Option (ScaledSolution n) :=
  if scan.found = none then some ⟨d,0⟩ else none

abbrev integerZero {m n : ℕ} (M : IntegerAugment m n) (d : ℤ) : Option (ScaledSolution n) :=
  zeroAnswer d (rhsScan M)

/-- An arithmetic charge for each bounded search, dense Bareiss update, and
back substitution. Testing or evaluating a scalar operation costs one. -/
def stageBudget (m n : ℕ) : ℕ := m*n + 4*m*(n+1) + (2*n+3) + m

structure Run (n : ℕ) where
  result : Option (ScaledSolution n)
  operations : ℕ

/-- Executable exact integer elimination. The returned solution uses a single
common denominator. The checked invariant guarantees exact divisions on a
run started at denominator one. -/
def runInt : (m n : ℕ) → IntegerAugment m n → ℤ → Run n
  | 0, _, _, d => ⟨some ⟨d,0⟩, 0⟩
  | _+1, 0, M, d =>
    let scan := rhsScan M
    ⟨zeroAnswer d scan, scan.tested.length⟩
  | m+1, n+1, M, d =>
    let scan := pivotScan M
    match scan.found with
    | none =>
      let rhs := rhsScan M
      ⟨zeroAnswer d rhs, scan.tested.length+rhs.tested.length⟩
    | some (i,j) =>
      let sub := runInt m n (forwardStep M d i j) (M i (some j))
      ⟨sub.result.map (backwardStep M i j),
        scan.tested.length+4*m*(n+1)+sub.operations+(if sub.result.isSome then 2*n+3 else 0)⟩

theorem stageBudget_mono {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    stageBudget m n ≤ stageBudget m' n' := by
  unfold stageBudget
  gcongr

theorem runInt_operations (m n : ℕ) (M : IntegerAugment m n) (d : ℤ) :
    (runInt m n M d).operations ≤ (min m n+1)*stageBudget m n := by
  induction m generalizing n d with
  | zero => simp [runInt]
  | succ m ih =>
    cases n with
    | zero =>
      have hh := rhsScan_length M
      simp [runInt, stageBudget]
      omega
    | succ n =>
      have hpLen := pivotScan_length M
      rw [runInt]
      dsimp only
      cases hp : (pivotScan M).found with
      | none =>
        have hrLen := rhsScan_length M
        refine le_trans ?_ (Nat.le_mul_of_pos_left _ (by omega))
        simp [stageBudget]
        omega
      | some p =>
        obtain ⟨i,j⟩ := p
        dsimp only
        have hmin : min (m+1) (n+1) = min m n+1 := by omega
        let sub := runInt m n (forwardStep M d i j) (M i (some j))
        have hsub := (ih n (forwardStep M d i j) (M i (some j))).trans
          (Nat.mul_le_mul_left _ (stageBudget_mono (Nat.le_succ m) (Nat.le_succ n)))
        have hl : 4*m*(n+1) ≤ 4*(m+1)*(n+1+1) := by gcongr <;> omega
        have hb : (if sub.result.isSome then 2*n+3 else 0) ≤ 2*(n+1)+3 := by split <;> omega
        have hstage : (pivotScan M).tested.length+4*m*(n+1)+(if sub.result.isSome then 2*n+3 else 0) ≤
            stageBudget (m+1) (n+1) := by unfold stageBudget; omega
        calc
          _ = sub.operations + ((pivotScan M).tested.length+4*m*(n+1)+(if sub.result.isSome then 2*n+3 else 0)) := by
            change (pivotScan M).tested.length+4*m*(n+1)+sub.operations+(if sub.result.isSome then 2*n+3 else 0) = _
            ac_rfl
          _ ≤ (min m n+1)*stageBudget (m+1) (n+1) + stageBudget (m+1) (n+1) := Nat.add_le_add hsub hstage
          _ = _ := by simp only [hmin, Nat.add_mul, one_mul]

end Reconstruction.BareissSolver
