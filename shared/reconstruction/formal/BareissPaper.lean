import BareissPaperOutput
import BareissPaperTraceCost

/-! Section 4.2: bit-operation accounting for generating the row systems,
performing fraction-free Gaussian elimination and writing all coefficients. -/

namespace Reconstruction.BareissPaper

open AffineEdge BareissHeight BareissSolver
open AffineCost.Bit (Fraction)
open scoped BigOperators

def rowCharge {q : ℕ} (L : ℕ) (a : Fin q → Fraction) (u : Word q) : ℕ :=
  let m := equationCount q
  let n := unknownCount q
  let table := buildTable a u
  table.steps + solverBitCharge (traceBits m n (generationWidth q L)+1) table.value

/-- Charge each generated system and the arithmetic trace on its own entries,
then the writes for the coefficient vectors selected by the successful run. -/
def constructionCharge {q : ℕ} (L : ℕ) (a : Fin q → Fraction) : ℕ :=
  (∑ i : Fin (wordCount q), rowCharge L a ((wordIndex q).symm i)) +
  (solveAll a).elim 0 (fun s => (emitMatrix L s).steps)

/-- A polynomial in the array size D, the slot count q and the label width L. -/
def constructionBudget (D q L : ℕ) : ℕ :=
  let m := q*D
  let n := D*q + q*(2*q+3)
  let w := generationWidth q L
  let b := 2*(m*(w+m)+1)+n+4
  D*(16+m*(n+1)*cellBudget D q L +
    ((m+1)*stageBudget m n)*scalarBudget b) +
    (16+D*D*(q+1)*(88*(m*(w+m)+2)^2+16))

theorem constructionCharge_le {q L : ℕ} (a : Fin q → Fraction) (ha : ∀ t, (a t).size ≤ L) :
    constructionCharge L a ≤ constructionBudget (wordCount q) q L := by
  let D := wordCount q
  let m := equationCount q
  let n := D*q + q*(2*q+3)
  let w := generationWidth q L
  let b := 2*(m*(w+m)+1)+n+4
  have hn : unknownCount q ≤ n := by
    unfold unknownCount measurementCount n D
    have hhalf := Nat.div_le_self (q+1) 2
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.sub_le q 2))
      (Nat.mul_le_mul_left q (by omega))
  have hmin : min m (unknownCount q+1) ≤ m := Nat.min_le_left .. 
  have hb : traceBits m (unknownCount q) w + 1 ≤ b := by
    unfold traceBits minorBits b
    gcongr
  have hsc : scalarBudget (traceBits m (unknownCount q) w + 1) ≤ scalarBudget b := by
    unfold scalarBudget
    gcongr
  let rowMax := 16+m*(n+1)*cellBudget D q L +
    ((m+1)*stageBudget m n)*scalarBudget b
  have hrow (u : Word q) : rowCharge L a u ≤ rowMax := by
    apply Nat.add_le_add
    · apply (buildTable_steps a u ha).trans
      change 16+m*(unknownCount q+1)*cellBudget D q L ≤ _
      gcongr
    · apply (solverBitCharge_le _ _).trans
      change ((min m (unknownCount q)+1)*stageBudget m (unknownCount q))*_ ≤ _
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.add_le_add_right (Nat.min_le_left ..) 1)
        (stageBudget_mono le_rfl hn)) hsc
  have hsum : (∑ i : Fin (wordCount q), rowCharge L a ((wordIndex q).symm i)) ≤ D*rowMax := by
    calc
      _ ≤ ∑ _ : Fin (wordCount q), rowMax := Finset.sum_le_sum fun _ _ => hrow _
      _ = _ := by simp [D]
  have hslots : coefficientSlots q ≤ q+1 := by unfold coefficientSlots; omega
  unfold constructionCharge
  apply Nat.add_le_add hsum
  cases hs : solveAll a with
  | none => exact Nat.zero_le _
  | some s =>
    apply (emitMatrix_steps L s).trans
    unfold outputBudget solutionWidth
    change 16+D*D*coefficientSlots q*(88*(m*(w+m)+1+1)^2+16) ≤
      16+D*D*(q+1)*(88*(m*(w+m)+2)^2+16)
    gcongr

/-- The original Gaussian construction, including the physical recovery
condition, serialization, every scalar operation's exact binary implementation,
and the uniform bit-operation bound. -/
theorem gaussian_reconstruction {q L : ℕ} (a : Fin q → Fraction) (hv : ∀ t, (a t).valid)
    (ha : ∀ t, (a t).size ≤ L) (hq : 2 ≤ q) (hi : Function.Injective (physicalLabels a))
    (hn : ∀ t, physicalLabels a t ≠ 0) :
    (∃ p : OutputMatrix q, paperOutput L a = some p ∧
      (∀ (i j : Fin (wordCount q)) (k : Fin (coefficientSlots q)), p[i.val][j.val][k.val].valid) ∧
      PairedCondition (physicalLabels a) (binaryEncoder q) (q-2) (outputPolynomial p)) ∧
    (∀ (u : Word q) (op : ScalarOp), op ∈ solveIntTrace (buildTable a u).value →
      (scalarProgram (traceBits (equationCount q) (unknownCount q) (generationWidth q L)+1) op).value.map
        (Sum.map id AffineCost.Bit.Signed.number) = some (scalarValue op)) ∧
    constructionCharge L a ≤ constructionBudget (wordCount q) q L := by
  refine ⟨paperOutput_spec a hv ha hq hi hn, fun u => ?_, constructionCharge_le a ha⟩
  apply solverTrace_bit_realizes
  simpa only [buildTable_value] using generatedInt_height a u ha

end Reconstruction.BareissPaper
