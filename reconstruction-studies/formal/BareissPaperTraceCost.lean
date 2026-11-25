import BareissPaperMaterialize
import BareissSolverBounds

/-!
Pricing for the verified scalar trace of the native table algorithm. The
operands of each recorded operation are written as signed bits, and the
corresponding checked bit routine is used.
-/

namespace Reconstruction.BareissPaper

open Reconstruction.BareissSolver
open AffineCost.Bit (Run Signed)
open scoped BigOperators

private def binaryProgram (B : ℕ) (a b : ℤ)
    (f : Signed → Signed → Run (Option Signed)) : Run (Option (Bool ⊕ Signed)) :=
  let x := writeSigned B a
  let y := writeSigned B b
  let z := f x.value y.value
  ⟨z.value.map Sum.inr, 8+x.steps+y.steps+z.steps⟩

private def liftSigned (f : Signed → Signed → Run Signed) (a b : Signed) : Run (Option Signed) :=
  let r := f a b
  ⟨some r.value,r.steps⟩

def scalarProgram (B : ℕ) : ScalarOp → Run (Option (Bool ⊕ Signed))
  | .testZero a =>
    let x := writeSigned B a
    let z := x.value.isZero
    ⟨some (.inl z.value),8+x.steps+z.steps⟩
  | .mul a b => binaryProgram B a b (liftSigned Signed.mul)
  | .add a b => binaryProgram B a b (liftSigned Signed.add)
  | .sub a b => binaryProgram B a b (liftSigned BareissArithmetic.subtract)
  | .exactDiv a b => binaryProgram B a b BareissArithmetic.exactDiv

def scalarValue : ScalarOp → Bool ⊕ ℤ
  | .testZero a => .inl (decide (a = 0))
  | .mul a b => .inr (a*b)
  | .add a b => .inr (a+b)
  | .sub a b => .inr (a-b)
  | .exactDiv a b => .inr (a/b)

private theorem operand_fit {C B : ℕ} {op : ScalarOp} (hC : C < 2^B)
    (h : op.Within C) {z : ℤ} (hz : z ∈ op.operands) : z.natAbs < 2^B :=
  (h z hz).trans_lt hC

theorem scalarProgram_correct {C B : ℕ} (op : ScalarOp)
    (hc : C < 2^B) (h : op.Within C) (hex : op.DivisionExact) :
    (scalarProgram B op).value.map (Sum.map id Signed.number) = some (scalarValue op) := by
  cases op with
  | testZero z =>
    have hz := operand_fit (z := z) hc h (by simp [ScalarOp.operands])
    have he : (writeSigned B z).value.isZero.value = decide (z = 0) := by
      apply Bool.eq_iff_iff.mpr
      rw [Signed.isZero_spec, writeSigned_number B z hz, decide_eq_true_eq]
    simp [scalarProgram, scalarValue, he]
  | mul a b =>
    have ha := operand_fit hc h (by simp [ScalarOp.operands] : a ∈ (ScalarOp.mul a b).operands)
    have hb := operand_fit hc h (by simp [ScalarOp.operands] : b ∈ (ScalarOp.mul a b).operands)
    simp [scalarProgram, binaryProgram, liftSigned, scalarValue, writeSigned_number, ha, hb]
  | add a b =>
    have ha := operand_fit hc h (by simp [ScalarOp.operands] : a ∈ (ScalarOp.add a b).operands)
    have hb := operand_fit hc h (by simp [ScalarOp.operands] : b ∈ (ScalarOp.add a b).operands)
    simp [scalarProgram, binaryProgram, liftSigned, scalarValue, writeSigned_number, ha, hb]
  | sub a b =>
    have ha := operand_fit hc h (by simp [ScalarOp.operands] : a ∈ (ScalarOp.sub a b).operands)
    have hb := operand_fit hc h (by simp [ScalarOp.operands] : b ∈ (ScalarOp.sub a b).operands)
    simp [scalarProgram, binaryProgram, liftSigned, scalarValue, writeSigned_number, ha, hb,
      BareissArithmetic.subtract_number]
  | exactDiv a b =>
    have ha := operand_fit hc h (by simp [ScalarOp.operands] : a ∈ (ScalarOp.exactDiv a b).operands)
    have hb := operand_fit hc h (by simp [ScalarOp.operands] : b ∈ (ScalarOp.exactDiv a b).operands)
    have hxa := writeSigned_number B a ha
    have hxb := writeSigned_number B b hb
    obtain ⟨hne, hdvd⟩ := hex
    obtain ⟨z, hz⟩ := BareissArithmetic.exactDiv_complete
      (by rwa [hxb]) (by rwa [hxa,hxb])
    have hz' := (BareissArithmetic.exactDiv_sound hz).2.1
    rw [hxa,hxb] at hz'
    simp [scalarProgram, binaryProgram, scalarValue, hz, hz']

def scalarBudget (B : ℕ) : ℕ := 32768*(B+1)^2

private theorem binaryProgram_steps (B : ℕ) (a b : ℤ)
    (f : Signed → Signed → Run (Option Signed))
    (h : ∀ x y, x.size ≤ B → y.size ≤ B → (f x y).steps ≤ 16384*(B+1)^2) :
    (binaryProgram B a b f).steps ≤ scalarBudget B := by
  have h₁ := writeSigned_steps B a
  have h₂ := writeSigned_steps B b
  have hf := h (writeSigned B a).value (writeSigned B b).value
    (writeSigned_size B a) (writeSigned_size B b)
  have hp : 0 < (B+1)^2 := by positivity
  simp only [binaryProgram, scalarBudget]
  omega

theorem scalarProgram_steps (B : ℕ) (op : ScalarOp) :
    (scalarProgram B op).steps ≤ scalarBudget B := by
  have hB : B+1 ≤ (B+1)^2 := by nlinarith
  have hsq (x y : Signed) (hx : x.size ≤ B) (hy : y.size ≤ B) :
      (x.size+y.size+1)^2 ≤ 4*(B+1)^2 := by
    calc
      _ ≤ (2*(B+1))^2 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  cases op with
  | testZero a =>
    have ha := writeSigned_steps B a
    have hsz := writeSigned_size B a
    have hz := Signed.isZero_steps (writeSigned B a).value
    have hp : 0 < (B+1)^2 := by positivity
    simp only [scalarProgram, scalarBudget]
    omega
  | mul a b =>
    apply binaryProgram_steps
    intro x y hx hy
    have hz := (Signed.mul_steps x y).trans (Nat.mul_le_mul_left 4096 (hsq x y hx hy))
    simp only [liftSigned]
    omega
  | add a b =>
    apply binaryProgram_steps
    intro x y hx hy
    have hz := Signed.add_steps x y
    simp only [liftSigned]
    omega
  | sub a b =>
    apply binaryProgram_steps
    intro x y hx hy
    have hz := BareissArithmetic.subtract_steps x y
    simp only [liftSigned]
    omega
  | exactDiv a b =>
    apply binaryProgram_steps
    intro x y hx hy
    have hz := (BareissArithmetic.exactDiv_steps x y).trans (Nat.mul_le_mul_left 2048 (hsq x y hx hy))
    omega

def solverBitCharge {m n : ℕ} (B : ℕ) (Z : IntegerAugment m n) : ℕ :=
  ((solveIntTrace Z).map (fun op => (scalarProgram B op).steps)).sum

theorem solverBitCharge_le {m n : ℕ} (B : ℕ) (Z : IntegerAugment m n) :
    solverBitCharge B Z ≤ ((min m n+1)*stageBudget m n)*scalarBudget B := by
  have hl : (solveIntTrace Z).length ≤ (min m n+1)*stageBudget m n :=
    (solveIntTrace_length Z).le.trans (solveIntScaled_operations Z)
  have h (ops : List ScalarOp) :
      (ops.map (fun op => (scalarProgram B op).steps)).sum ≤ ops.length*scalarBudget B := by
    induction ops with
    | nil => simp
    | cons op ops ih =>
      have hu := scalarProgram_steps B op
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
      omega
  exact (h _).trans (Nat.mul_le_mul_right _ hl)

theorem solverTrace_bit_realizes {m n b : ℕ} (Z : IntegerAugment m n)
    (h : ∀ i j, (Z i j).natAbs ≤ 2^b) :
    ∀ op ∈ solveIntTrace Z,
      (scalarProgram (traceBits m n b+1) op).value.map (Sum.map id Signed.number) =
        some (scalarValue op) := by
  intro op ho
  obtain ⟨hw, hex⟩ := solveInt_trace_height Z h op ho
  have hp : 0 < (2:ℕ)^traceBits m n b := by positivity
  apply scalarProgram_correct op _ hw hex
  rw [pow_succ]
  omega

end Reconstruction.BareissPaper
