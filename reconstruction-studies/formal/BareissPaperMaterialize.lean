import BareissPaperInput

/-!
Materialization of solver matrices and of signed numerators and denominators.
The counters charge traversals, cell writes, shifts and signed arithmetic.
-/

namespace Reconstruction.BareissPaper

open AffineEdge BareissHeight
open AffineCost.Bit (Run Word Signed Fraction)
open scoped BigOperators

/-- Reading a little-endian word by shifts and additions. -/
def readMagnitude : AffineCost.Bit.Word → Run ℕ
  | [] => ⟨0, 8⟩
  | b :: bs =>
    let t := readMagnitude bs
    ⟨AffineCost.Bit.digit b + 2*t.value, 16+8*(bs.length+1)+t.steps⟩

@[simp] theorem readMagnitude_value (xs : AffineCost.Bit.Word) :
    (readMagnitude xs).value = AffineCost.Bit.value xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [readMagnitude, ih]

theorem readMagnitude_steps (xs : AffineCost.Bit.Word) :
    (readMagnitude xs).steps ≤ 32*(xs.length+1)^2 := by
  induction xs with
  | nil => decide
  | cons b bs ih =>
    simp only [readMagnitude, List.length_cons]
    nlinarith

def readSigned (a : Signed) : Run ℤ :=
  let p := readMagnitude a.plus
  let n := readMagnitude a.minus
  ⟨(p.value : ℤ) - n.value, 8 + p.steps + n.steps + 32*(a.size+1)⟩

@[simp] theorem readSigned_value (a : Signed) : (readSigned a).value = a.number := by
  simp [readSigned, Signed.number]

theorem readSigned_steps (a : Signed) (W : ℕ) (h : a.size ≤ W) :
    (readSigned a).steps ≤ 128*(W+1)^2 := by
  have hp := readMagnitude_steps a.plus
  have hn := readMagnitude_steps a.minus
  have hpW : a.plus.length ≤ W := (le_max_left _ _).trans h
  have hnW : a.minus.length ≤ W := (le_max_right _ _).trans h
  have hp' : (a.plus.length+1)^2 ≤ (W+1)^2 := Nat.pow_le_pow_left (by omega) _
  have hn' : (a.minus.length+1)^2 ≤ (W+1)^2 := Nat.pow_le_pow_left (by omega) _
  simp only [readSigned]
  have hW : W+1 ≤ (W+1)^2 := by nlinarith
  omega

/-- One encoded cell, followed by the linear-word reading operation for the solver. -/
def cellRun {q : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q)
    (i : Fin (equationCount q)) (j : Option (Fin (unknownCount q))) : Run ℤ :=
  let r := buildEntry a u ((equationIndex q).symm i) (j.map (unknownIndex q).symm)
  let s := readSigned r.value
  ⟨s.value, 16+r.steps+s.steps⟩

@[simp] theorem cellRun_value {q : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q) (i j) :
    (cellRun a u i j).value = generatedInt a u i j := by simp [cellRun, generatedInt]

def cellBudget (D q L : ℕ) : ℕ :=
  16+entryBudget D q L+128*(generationWidth q L+1)^2

theorem cellRun_steps {q L : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q)
    (h : ∀ t, (a t).size ≤ L) (i j) :
    (cellRun a u i j).steps ≤ cellBudget (wordCount q) q L := by
  have h₁ := buildEntry_steps a u h ((equationIndex q).symm i) (j.map (unknownIndex q).symm)
  have h₂ := readSigned_steps
    (buildEntry a u ((equationIndex q).symm i) (j.map (unknownIndex q).symm)).value _
    (buildEntry_size a u h _ _)
  simp only [cellRun, cellBudget]
  omega

def columnSlot {n : ℕ} (i : Fin (n+1)) : Option (Fin n) := Fin.cases (motive := fun _ => Option (Fin n)) none some i

/-- Materialize every cell once. The optional column is stored first. -/
def buildTable {q : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q) :
    Run (Matrix (Fin (equationCount q)) (Option (Fin (unknownCount q))) ℤ) :=
  let rows := Vector.ofFn (fun i : Fin (equationCount q) =>
    Vector.ofFn (fun j : Fin (unknownCount q+1) => (cellRun a u i (columnSlot j)).value))
  ⟨Matrix.of (fun i j => rows[i.val][(j.elim (0 : Fin (unknownCount q+1)) Fin.succ).val]),
    16 + ∑ i : Fin (equationCount q), ∑ j : Fin (unknownCount q+1),
      (cellRun a u i (columnSlot j)).steps⟩

@[simp] theorem buildTable_value {q : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q) :
    (buildTable a u).value = generatedInt a u := by
  ext i j
  cases j <;> simp [buildTable, columnSlot]

theorem buildTable_steps {q L : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q)
    (h : ∀ t, (a t).size ≤ L) :
    (buildTable a u).steps ≤
      16+equationCount q*(unknownCount q+1)*cellBudget (wordCount q) q L := by
  simp only [buildTable]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _ : Fin (equationCount q), ∑ _ : Fin (unknownCount q+1),
      cellBudget (wordCount q) q L :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun _ _ => cellRun_steps a u h _ _))
    _ = _ := by simp [Nat.mul_assoc]

/-- Fixed-width binary writing. The low bit and shift can be implemented by
reading one bit and moving over the remaining word. -/
def writeMagnitude : ℕ → ℕ → Run AffineCost.Bit.Word
  | 0, _ => ⟨[], 8⟩
  | B+1, x =>
    let t := writeMagnitude B (x/2)
    ⟨decide (x%2 = 1) :: t.value, 16+8*(B+1)+t.steps⟩

@[simp] theorem writeMagnitude_length (B x : ℕ) : (writeMagnitude B x).value.length = B := by
  induction B generalizing x with
  | zero => rfl
  | succ B ih => simp [writeMagnitude, ih]

theorem writeMagnitude_value (B x : ℕ) (h : x < 2^B) :
    AffineCost.Bit.value (writeMagnitude B x).value = x := by
  induction B generalizing x with
  | zero =>
    simp only [pow_zero] at h
    have hx : x = 0 := by omega
    simp [writeMagnitude, hx]
  | succ B ih =>
    have hq : x/2 < 2^B := Nat.div_lt_of_lt_mul (by simpa only [pow_succ, Nat.mul_comm] using h)
    have hs := Nat.mod_add_div x 2
    have hr := Nat.mod_lt x (by decide : 0 < 2)
    simp only [writeMagnitude, AffineCost.Bit.value_cons, ih _ hq, AffineCost.Bit.digit]
    by_cases hu : x % 2 = 1 <;> simp [hu] <;> omega

theorem writeMagnitude_steps (B x : ℕ) : (writeMagnitude B x).steps ≤ 32*(B+1)^2 := by
  induction B generalizing x with
  | zero => simp [writeMagnitude]
  | succ B ih =>
    have ht := ih (x/2)
    simp only [writeMagnitude]
    nlinarith

def writeSigned (B : ℕ) (z : ℤ) : Run Signed :=
  let w := writeMagnitude B z.natAbs
  ⟨(if z < 0 then ⟨[], w.value⟩ else ⟨w.value, []⟩), 8+w.steps⟩

theorem writeSigned_number (B : ℕ) (z : ℤ) (h : z.natAbs < 2^B) :
    (writeSigned B z).value.number = z := by
  simp only [writeSigned]
  split
  · simp only [Signed.number, AffineCost.Bit.value_nil, writeMagnitude_value _ _ h,
      Nat.cast_zero, zero_sub]
    omega
  · simp only [Signed.number, AffineCost.Bit.value_nil, writeMagnitude_value _ _ h,
      Nat.cast_zero, sub_zero]
    omega

theorem writeSigned_size (B : ℕ) (z : ℤ) : (writeSigned B z).value.size ≤ B := by
  simp only [writeSigned]
  split <;> simp [Signed.size]

theorem writeSigned_steps (B : ℕ) (z : ℤ) : (writeSigned B z).steps ≤ 40*(B+1)^2 := by
  have h := writeMagnitude_steps B z.natAbs
  simp only [writeSigned]
  have hp : 0 < (B+1)^2 := by positivity
  omega

def writeFraction (B : ℕ) (n d : ℤ) : Run Fraction :=
  let a := writeSigned B n
  let b := writeSigned B d
  ⟨⟨a.value,b.value⟩, 8+a.steps+b.steps⟩

theorem writeFraction_spec (B : ℕ) (n d : ℤ) (hn : n.natAbs < 2^B)
    (hd : d.natAbs < 2^B) (hne : d ≠ 0) :
    (writeFraction B n d).value.valid ∧ (writeFraction B n d).value.rat = (n:ℚ)/d := by
  simp [writeFraction, Fraction.valid, Fraction.rat, writeSigned_number, hn, hd, hne]

theorem writeFraction_steps (B : ℕ) (n d : ℤ) :
    (writeFraction B n d).steps ≤ 88*(B+1)^2 := by
  have h := writeSigned_steps B n
  have h' := writeSigned_steps B d
  have hp : 0 < (B+1)^2 := by positivity
  simp only [writeFraction]
  omega

end Reconstruction.BareissPaper
