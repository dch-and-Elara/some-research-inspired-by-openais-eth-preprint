import BareissHeightEncoder
import Mathlib.Algebra.BigOperators.Fin

/-!
The executable Fin-indexed augmented matrix for the generic solver. All
index equivalences are positional and computable. Column `none` is the RHS.
-/

namespace BareissHeight

open AffineEdge
open scoped BigOperators

def wordCount (q : ℕ) : ℕ := 4^q
def measurementCount (q : ℕ) : ℕ := q + ((q+1)/2 + 2)
def equationCount (q : ℕ) : ℕ := q * wordCount q
def unknownCount (q : ℕ) : ℕ := wordCount q * (q-2) + q * measurementCount q

def bitsIndex (q : ℕ) : Bits q ≃ Fin (2^q) :=
  (Equiv.piCongrRight fun _ : Fin q => finTwoEquiv.symm).trans finFunctionFinEquiv

def wordIndex (q : ℕ) : Word q ≃ Fin (wordCount q) :=
  (Equiv.prodCongr (bitsIndex q) (bitsIndex q)).trans (finProdFinEquiv.trans
    (finCongr (by simpa only [wordCount] using (mul_pow (2:ℕ) 2 q).symm)))

def measurementIndex (q : ℕ) : EncoderRow q ≃ Fin (measurementCount q) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.refl _) finTwoEquiv.symm).trans finSumFinEquiv)).trans finSumFinEquiv

def equationIndex (q : ℕ) : Equation q ≃ Fin (equationCount q) :=
  (Equiv.prodCongr (Equiv.refl _) (wordIndex q)).trans finProdFinEquiv

def unknownIndex (q : ℕ) : Unknown q ≃ Fin (unknownCount q) :=
  (Equiv.sumCongr
    ((Equiv.prodCongr (wordIndex q) (Equiv.refl _)).trans finProdFinEquiv)
    ((Equiv.prodCongr (Equiv.refl _) (measurementIndex q)).trans finProdFinEquiv)).trans finSumFinEquiv

/-- Each coefficient is computed from the row's label and the encoded indices. -/
def denseEncoderInt {q : ℕ} (sites : Fin q → ℚ) (u : Word q) :
    Matrix (Fin (equationCount q)) (Option (Fin (unknownCount q))) ℤ :=
  (encoderInt sites u).submatrix (equationIndex q).symm (fun j => j.map (unknownIndex q).symm)

def decodeSolution {q : ℕ} (x : Fin (unknownCount q) → ℚ) (j : Unknown q) : ℚ :=
  x (unknownIndex q j)

theorem denseEncoder_system_iff {q : ℕ} (sites : Fin q → ℚ) (u : Word q)
    (x : Fin (unknownCount q) → ℚ) :
    (∀ i, (∑ j, (denseEncoderInt sites u i (some j) : ℚ) * x j) =
      (denseEncoderInt sites u i none : ℚ)) ↔
      (∀ e, (∑ j, (encoderInt sites u e (some j) : ℚ) * decodeSolution x j) =
        (encoderInt sites u e none : ℚ)) := by
  have hsum (e : Equation q) :
      (∑ j, (denseEncoderInt sites u (equationIndex q e) (some j) : ℚ) * x j) =
        ∑ j, (encoderInt sites u e (some j) : ℚ) * decodeSolution x j := by
    rw [← (unknownIndex q).sum_comp
      (fun j => (denseEncoderInt sites u (equationIndex q e) (some j) : ℚ) * x j)]
    simp [denseEncoderInt, Matrix.submatrix_apply, decodeSolution]
  constructor
  · intro hs e
    have hh := hs (equationIndex q e)
    rw [hsum] at hh
    simpa [denseEncoderInt, Matrix.submatrix_apply] using hh
  · intro hs i
    obtain ⟨e, rfl⟩ := (equationIndex q).surjective i
    rw [hsum]
    simpa [denseEncoderInt, Matrix.submatrix_apply] using hs e

theorem denseEncoder_consistent {q : ℕ} (sites : Fin q → ℚ) (u : Word q)
    (hq : 2 ≤ q) (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    ∃ x : Fin (unknownCount q) → ℚ, ∀ i,
      (∑ j, (denseEncoderInt sites u i (some j) : ℚ) * x j) =
        (denseEncoderInt sites u i none : ℚ) := by
  obtain ⟨x, hx⟩ := encoderInt_consistent sites u hq hi hn
  refine ⟨x ∘ (unknownIndex q).symm,
    (denseEncoder_system_iff sites u (x ∘ (unknownIndex q).symm)).mpr ?_⟩
  simpa [decodeSolution] using hx

theorem paired_of_denseEncoder_solutions {q : ℕ} (sites : Fin q → ℚ)
    (x : Word q → Fin (unknownCount q) → ℚ)
    (h : ∀ u i, (∑ j, (denseEncoderInt sites u i (some j) : ℚ) * x u j) =
      (denseEncoderInt sites u i none : ℚ)) :
    PairedCondition sites (binaryEncoder q) (q-2)
      (fun u => solutionPolynomial u (decodeSolution (x u))) :=
  paired_of_encoderInt_solutions sites (fun u => decodeSolution (x u))
    (fun u => (denseEncoder_system_iff sites u (x u)).mp (h u))

theorem denseEncoder_height {q b : ℕ} (sites : Fin q → ℚ) (u : Word q)
    (h : ∀ t, RatHeight b (sites t)) (i : Fin (equationCount q)) (j : Option (Fin (unknownCount q))) :
    (denseEncoderInt sites u i j).natAbs ≤ 2^(b*(q-2)) :=
  encoderInt_height sites u h _ _

theorem denseEncoder_entry_bits {q b : ℕ} (sites : Fin q → ℚ) (u : Word q)
    (h : ∀ t, RatHeight b (sites t)) (i : Fin (equationCount q)) (j : Option (Fin (unknownCount q))) :
    (denseEncoderInt sites u i j).natAbs.size + 1 ≤ b*(q-2)+2 := by
  apply Nat.add_le_add_right
  apply Nat.size_le.mpr
  have hpos : 0 < (2:ℕ)^(b*(q-2)) := by positivity
  rw [pow_succ]
  exact (denseEncoder_height sites u h i j).trans_lt (by omega)

/-- The number of entries of a single augmented solver input, in the paper's
D=4^q physical coordinates and m=q+⌈q/2⌉+2 measurement coordinates. -/
theorem denseEncoder_entry_count (q : ℕ) :
    Fintype.card (Fin (equationCount q) × Option (Fin (unknownCount q))) =
      (q*4^q)*(4^q*(q-2)+q*(q+((q+1)/2+2))+1) := by
  simp [equationCount, unknownCount, measurementCount, wordCount, Nat.add_comm]

theorem denseEncoder_family_entry_count (q : ℕ) :
    Fintype.card (Word q × Fin (equationCount q) × Option (Fin (unknownCount q))) =
      4^q*((q*4^q)*(4^q*(q-2)+q*(q+((q+1)/2+2))+1)) := by
  rw [Fintype.card_prod, Fintype.card_congr (wordIndex q), Fintype.card_fin,
    denseEncoder_entry_count, wordCount]

/-- The total signed-magnitude payload across all output systems, before
any solver workspace or delimiters. -/
theorem denseEncoder_family_payload_bits {q b : ℕ} (sites : Fin q → ℚ)
    (h : ∀ t, RatHeight b (sites t)) :
    (∑ p : Word q × Fin (equationCount q) × Option (Fin (unknownCount q)),
      ((denseEncoderInt sites p.1 p.2.1 p.2.2).natAbs.size + 1)) ≤
      (4^q*((q*4^q)*(4^q*(q-2)+q*(q+((q+1)/2+2))+1))) * (b*(q-2)+2) := by
  calc
    _ ≤ ∑ _ : Word q × Fin (equationCount q) × Option (Fin (unknownCount q)),
        (b*(q-2)+2) := Finset.sum_le_sum (fun p _ => denseEncoder_entry_bits sites p.1 h p.2.1 p.2.2)
    _ = _ := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ, denseEncoder_family_entry_count]

/-- A common signed width for all original minors of one solver input. -/
theorem denseEncoder_minor_bits {q b : ℕ} {K : Type*} [Fintype K] [DecidableEq K]
    (sites : Fin q → ℚ) (u : Word q) (h : ∀ t, RatHeight b (sites t))
    (r : K ↪ Fin (equationCount q)) (c : K → Option (Fin (unknownCount q))) :
    ((denseEncoderInt sites u).submatrix r c).det.natAbs.size + 1 ≤
      equationCount q*(b*(q-2)+equationCount q)+2 := by
  have hk : Fintype.card K ≤ equationCount q := by
    simpa using Fintype.card_le_of_injective r r.injective
  have hmul := Nat.mul_le_mul hk (Nat.add_le_add_left hk (b*(q-2)))
  have hsize := minor_size_le (denseEncoderInt sites u) r c (b*(q-2))
    (denseEncoder_height sites u h)
  omega

end BareissHeight
