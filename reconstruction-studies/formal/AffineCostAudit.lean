import AffineCompile

open AffineEdge
open scoped Polynomial

namespace AffineCost

open Bit

/-- Uniform decoder for the encoder of §4.2. The list carries the encoded
labels. Each result chunk contains one rational polynomial coefficient. -/
def decoder (as : List Fraction) (q : ℕ) : Run (List Bit.Word) :=
  runCompiledOutput as (AffineCompile.compile q)

/-- Polynomial in the physical word count, slot count and label bit width. -/
def decoderBound (D q L : ℕ) : ℕ :=
  AffineCompile.generationBound D q + executionBound D q L

theorem decoder_bit_complexity (as : List Fraction) (q L : ℕ)
    (h : ∀ a ∈ as, a.size ≤ L) : (decoder as q).steps ≤ decoderBound (4^q) q L := by
  exact (runCompiledOutput_bound as (AffineCompile.compile q) L h
      (AffineCompile.compile_value q)).trans
    (Nat.add_le_add_right (AffineCompile.compile_steps q) _)

theorem decoder_correct (as : List Fraction) (q : ℕ)
    (hv : ∀ a ∈ as, a.valid) (hq : 2 ≤ q)
    (hi : Function.Injective (bitSites as : Fin q → ℚ))
    (hn : ∀ t : Fin q, bitSites as t ≠ 0) :
    ∃ P, PairedCondition (bitSites as) (binaryEncoder q) (q-2) P ∧
      (decoder as q).value.map (fun s => (readFraction s).map fun p => p.1.rat) =
        (tasks q).map (fun t => some ((P t.1 t.2.1).coeff t.2.2.val)) :=
  runCompiledOutput_correct as (AffineCompile.compile q) (AffineCompile.compile_value q) hv hq hi hn

theorem decoder_output_valid (as : List Fraction) (q : ℕ) (hv : ∀ a ∈ as, a.valid)
    (s : Bit.Word) (hs : s ∈ (decoder as q).value) :
    ∃ a, readFraction s = some (a,[]) ∧ a.valid :=
  runCompiledOutput_valid as (AffineCompile.compile q) (AffineCompile.compile_value q) hv s hs

/- Execute the complete compiler, bit evaluator and writer at q=2. -/
#eval
  let labels : List Fraction :=
    [⟨⟨[],[false,true]⟩,⟨[true,true],[]⟩⟩,
     ⟨⟨[true,true,true],[]⟩,⟨[false,false,true],[]⟩⟩]
  let r := decoder labels 2
  let expected : List (Option ℚ) := (tasks 2).map fun t =>
    some (if t.2.2.val = 0 ∧ wordEqual t.1 t.2.1 = true then 1 else 0)
  let decoded := r.value.map (fun s => (readFraction s).map fun p => p.1.rat)
  (r.value.length, decoded == expected, r.steps)

#print axioms decoder_correct
#print axioms decoder_bit_complexity
#print axioms decoder_output_valid

end AffineCost
