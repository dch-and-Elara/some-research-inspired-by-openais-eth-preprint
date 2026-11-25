import BareissPaperMaterialize
import BareissSolver

/-!
Composition of exact input generation, deterministic solver completeness,
and the writing of all coefficient pairs. The rational numbers represented
by the output pairs are interpreted only in the specification.
-/

namespace Reconstruction.BareissPaper

open AffineEdge BareissHeight
open AffineCost.Bit (Run Fraction)
open Reconstruction.BareissSolver
open Polynomial
open scoped Polynomial BigOperators

def solutionWidth (q L : ℕ) : ℕ :=
  equationCount q * (generationWidth q L + equationCount q) + 1

def solveRow {q : ℕ} (a : Fin q → Fraction) (u : Word q) : BareissSolver.Run (unknownCount q) :=
  solveIntScaled (buildTable a u).value

theorem solveRow_complete {q : ℕ} (a : Fin q → Fraction) (u : Word q)
    (hv : ∀ t, (a t).valid) (hq : 2 ≤ q)
    (hi : Function.Injective (physicalLabels a)) (hn : ∀ t, physicalLabels a t ≠ 0) :
    ∃ s, (solveRow a u).result = some s := by
  obtain ⟨x,hx⟩ := generated_consistent a u hv hq hi hn
  have he : (solveRow a u).result.isSome :=
    (solveIntScaled_spec _).1.mpr ⟨x, by simpa [Solves] using hx⟩
  cases hs : (solveRow a u).result with
  | none => simp [hs] at he
  | some s => exact ⟨s,rfl⟩

theorem solveRow_spec {q L : ℕ} (a : Fin q → Fraction) (u : Word q)
    (ha : ∀ t, (a t).size ≤ L) {s : ScaledSolution (unknownCount q)}
    (hs : (solveRow a u).result = some s) :
    (∀ i, ∑ j, (generatedInt a u i (some j) : ℚ) * s.rational j =
      (generatedInt a u i none : ℚ)) ∧ s.denominator ≠ 0 ∧
      s.denominator.natAbs < 2^solutionWidth q L ∧
      ∀ j, (s.numerator j).natAbs < 2^solutionWidth q L := by
  obtain ⟨hsolve,hne,k,hk,hD,hN⟩ := (solveIntScaled_spec _).2 s hs
  have hm (z : ℤ) (hz : HasMinor (buildTable a u).value k z) :
      z.natAbs < 2^solutionWidth q L := by
    obtain ⟨r,c,rfl⟩ := hz
    have hM (i j) : ((buildTable a u).value i j).natAbs ≤ 2^generationWidth q L :=
      buildTable_value a u ▸ generatedInt_height a u ha i j
    have hb := minor_lt_pow _ r c (generationWidth q L) hM
    rw [Fintype.card_fin] at hb
    have hk' := hk.trans (Nat.min_le_left ..)
    refine hb.trans_le (Nat.pow_le_pow_right (by decide) ?_)
    unfold solutionWidth
    gcongr
  refine ⟨by simpa [Solves] using hsolve,hne,hm _ hD,fun j => ?_⟩
  rcases hN j with h0 | hj
  · simp [h0]
  · exact hm _ hj

/-- Run every output-row system in the positional order of the physical words. -/
def solveAll {q : ℕ} (a : Fin q → Fraction) :
    Option (Vector (ScaledSolution (unknownCount q)) (wordCount q)) :=
  (Vector.ofFn fun i => (solveRow a ((wordIndex q).symm i)).result).mapM id

theorem solveAll_complete {q : ℕ} (a : Fin q → Fraction)
    (hv : ∀ t, (a t).valid) (hq : 2 ≤ q)
    (hi : Function.Injective (physicalLabels a)) (hn : ∀ t, physicalLabels a t ≠ 0) :
    ∃ s : Vector (ScaledSolution (unknownCount q)) (wordCount q),
      solveAll a = some s ∧ ∀ i : Fin (wordCount q),
        (solveRow a ((wordIndex q).symm i)).result = some s[i.val] := by
  classical
  choose s hs using fun i : Fin (wordCount q) =>
    solveRow_complete a ((wordIndex q).symm i) hv hq hi hn
  refine ⟨Vector.ofFn s, ?_, by simpa using hs⟩
  have he : (Vector.ofFn fun i : Fin (wordCount q) => (solveRow a ((wordIndex q).symm i)).result) =
      (Vector.ofFn s).map some := by
    apply Vector.ext
    intro i hi'
    simpa using hs ⟨i,hi'⟩
  rw [solveAll, he, Vector.mapM_map]
  calc
    _ = some ((Vector.ofFn s).map id) := Vector.mapM_pure (m := Option) id
    _ = _ := by simp

def coefficientSlots (q : ℕ) : ℕ := (q-2)+1

abbrev OutputMatrix (q : ℕ) :=
  Vector (Vector (Vector Fraction (coefficientSlots q)) (wordCount q)) (wordCount q)

def emitCoefficient {q : ℕ} (L : ℕ) (u v : Word q) (s : ScaledSolution (unknownCount q)) :
    Fin (coefficientSlots q) → Run Fraction :=
  Fin.cases (motive := fun _ => Run Fraction)
    (writeFraction (solutionWidth q L) (if u = v then 1 else 0) 1)
    (fun j => writeFraction (solutionWidth q L) (s.numerator (unknownIndex q (.inl (v,j)))) s.denominator)

noncomputable def interpretCoefficient {q : ℕ} (u v : Word q)
    (s : ScaledSolution (unknownCount q)) : Fin (coefficientSlots q) → ℚ :=
  Fin.cases (motive := fun _ => ℚ) (constantEntry u v)
    (fun j => s.rational (unknownIndex q (.inl (v,j))))

theorem emitCoefficient_spec {q L : ℕ} (u v : Word q)
    (s : ScaledSolution (unknownCount q)) (hne : s.denominator ≠ 0)
    (hd : s.denominator.natAbs < 2^solutionWidth q L)
    (hn : ∀ j, (s.numerator j).natAbs < 2^solutionWidth q L)
    (j : Fin (coefficientSlots q)) :
    (emitCoefficient L u v s j).value.valid ∧
      (emitCoefficient L u v s j).value.rat = interpretCoefficient u v s j := by
  have hW : (1:ℕ) < 2^solutionWidth q L := Nat.one_lt_two_pow (by unfold solutionWidth; omega)
  refine Fin.cases ?_ (fun k => ?_) j
  · have hf : (if u = v then (1:ℤ) else 0).natAbs < 2^solutionWidth q L := by
      split <;> simp_all
    simpa [emitCoefficient, interpretCoefficient, constantEntry] using
      writeFraction_spec (solutionWidth q L) (if u = v then (1:ℤ) else 0) 1 hf hW (by decide)
  · simpa [emitCoefficient, interpretCoefficient] using
      writeFraction_spec (solutionWidth q L) (s.numerator (unknownIndex q (.inl (v,k))))
        s.denominator (hn _) hd hne

theorem emitCoefficient_steps {q L : ℕ} (u v : Word q)
    (s : ScaledSolution (unknownCount q)) (j : Fin (coefficientSlots q)) :
    (emitCoefficient L u v s j).steps ≤ 88*(solutionWidth q L+1)^2 := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa [emitCoefficient] using writeFraction_steps (solutionWidth q L) (if u = v then 1 else 0) 1
  · simpa [emitCoefficient] using
      writeFraction_steps (solutionWidth q L) (s.numerator (unknownIndex q (.inl (v,k)))) s.denominator

/-- Write every rational coefficient as two signed binary words. -/
def emitMatrix {q : ℕ} (L : ℕ) (s : Vector (ScaledSolution (unknownCount q)) (wordCount q)) :
    AffineCost.Bit.Run (OutputMatrix q) :=
  let emit (i j : Fin (wordCount q)) (k : Fin (coefficientSlots q)) :=
    emitCoefficient L ((wordIndex q).symm i) ((wordIndex q).symm j) s[i.val] k
  ⟨Vector.ofFn (fun i => Vector.ofFn (fun j => Vector.ofFn (fun k => (emit i j k).value))),
    16+ ∑ i : Fin (wordCount q), ∑ j : Fin (wordCount q), ∑ k : Fin (coefficientSlots q),
      ((emit i j k).steps + 16)⟩

def outputBudget (D q L : ℕ) : ℕ :=
  16+D*D*coefficientSlots q*(88*(solutionWidth q L+1)^2+16)

theorem emitMatrix_steps {q : ℕ} (L : ℕ) (s : Vector (ScaledSolution (unknownCount q)) (wordCount q)) :
    (emitMatrix L s).steps ≤ outputBudget (wordCount q) q L := by
  simp only [emitMatrix, outputBudget]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _i : Fin (wordCount q), ∑ _j : Fin (wordCount q), ∑ _k : Fin (coefficientSlots q),
        (88*(solutionWidth q L+1)^2+16) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact Nat.add_le_add_right (emitCoefficient_steps _ _ _ _ ) _
    _ = _ := by simp [Nat.mul_assoc]

def paperOutput {q : ℕ} (L : ℕ) (a : Fin q → Fraction) : Option (OutputMatrix q) :=
  (solveAll a).map fun s => (emitMatrix L s).value

noncomputable def outputPolynomial {q : ℕ} (p : OutputMatrix q) (u v : Word q) : ℚ[X] :=
  ∑ k : Fin (coefficientSlots q),
    Polynomial.C (p[(wordIndex q u).val][(wordIndex q v).val][k.val].rat) * X^k.val

/-- Unconditional success and correctness on admissible encoded label inputs. -/
theorem paperOutput_spec {q L : ℕ} (a : Fin q → Fraction) (hv : ∀ t, (a t).valid)
    (ha : ∀ t, (a t).size ≤ L) (hq : 2 ≤ q) (hi : Function.Injective (physicalLabels a))
    (hn : ∀ t, physicalLabels a t ≠ 0) :
    ∃ p : OutputMatrix q, paperOutput L a = some p ∧
      (∀ (i j : Fin (wordCount q)) (k : Fin (coefficientSlots q)), p[i.val][j.val][k.val].valid) ∧
      PairedCondition (physicalLabels a) (binaryEncoder q) (q-2) (outputPolynomial p) := by
  obtain ⟨s, hs, hrun⟩ := solveAll_complete a hv hq hi hn
  let p := (emitMatrix L s).value
  let x (u : Word q) := s[(wordIndex q u).val].rational
  have hprec (i j : Fin (wordCount q)) (k : Fin (coefficientSlots q)) :
      p[i.val][j.val][k.val].valid ∧
        p[i.val][j.val][k.val].rat =
          interpretCoefficient ((wordIndex q).symm i) ((wordIndex q).symm j) s[i.val] k := by
    obtain ⟨_, he, hd, hm⟩ := solveRow_spec a ((wordIndex q).symm i) ha (hrun i)
    simpa [p, emitMatrix] using emitCoefficient_spec (L := L) _ _ s[i.val] he hd hm k
  refine ⟨p, by simp [paperOutput,hs,p], fun i j k => (hprec i j k).1, ?_⟩
  have hp (u v : Word q) : outputPolynomial p u v = solutionPolynomial u (decodeSolution (x u)) v := by
    unfold outputPolynomial
    simp_rw [(hprec (wordIndex q u) (wordIndex q v) _).2, Equiv.symm_apply_apply]
    change (∑ k : Fin ((q-2)+1), Polynomial.C (interpretCoefficient u v _ k) * X^k.val) = _
    rw [Fin.sum_univ_succ]
    simp [interpretCoefficient, solutionPolynomial, x, decodeSolution]
  have hc := paired_of_generated_solutions a hv x
    (fun u i => by
      have hh := (solveRow_spec a ((wordIndex q).symm (wordIndex q u)) ha (hrun (wordIndex q u))).1 i
      simpa [x] using hh)
  exact (funext (fun u => funext (hp u))) ▸ hc

end Reconstruction.BareissPaper
