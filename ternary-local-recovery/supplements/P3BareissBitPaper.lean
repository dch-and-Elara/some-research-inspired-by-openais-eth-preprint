import P3BareissBitRun
import BareissPaper

open scoped BigOperators

namespace Paper3.BareissBit

open AffineEdge BareissHeight
open Reconstruction.BareissSolver Reconstruction.BareissPaper
open AffineCost.Bit (Run Fraction)

/-- Per recorded local access/control block in the dense bounded-word cost
model. A scan over all m-by-(n+1) cells of the padded representation,
with a constant number of accesses/copies and binary cursor operations,
is allowed per block. The field/row arithmetic is charged separately. -/
def navigation (m n B : ℕ) : ℕ := 64*(m+n+2)^2*(2*B+4)

theorem navigation_mono {m n m' n' B B' : ℕ} (hm : m ≤ m') (hn : n ≤ n')
    (hb : B ≤ B') : navigation m n B ≤ navigation m' n' B' := by
  unfold navigation
  gcongr

def bitWidth (q L : ℕ) : ℕ :=
  traceBits (equationCount q) (unknownCount q) (generationWidth q L) + 1

def rowClock (m n B : ℕ) : ℕ :=
  (m*(n+1)+1)*navigation m n B +
    (m+1)*branchCap m n B (navigation m n B)

theorem rowClock_mono {m n m' n' B B' : ℕ} (hm : m ≤ m') (hn : n ≤ n')
    (hb : B ≤ B') : rowClock m n B ≤ rowClock m' n' B' := by
  have hnav := navigation_mono hm hn hb
  have hbr := branchCap_mono hm hn hb hnav
  unfold rowClock
  gcongr

private theorem run_eq {α : Type} {r s : Run α} (hv : r.value = s.value)
    (ht : r.steps = s.steps) : r = s := by
  cases r
  cases s
  cases hv
  cases ht
  rfl

/-- The input recorder shares the exact computed cell runs between its
dense table and its proof-only bill. -/
def buildInputOnce {q : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q) :=
  onDenseTable (cellRun a u) 16

theorem buildInputOnce_eq {q : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q) :
    buildInputOnce a u = buildTable a u := by
  apply run_eq
  · ext i j
    simp [buildInputOnce]
  · simp [buildInputOnce,onDenseTable,buildTable]

/-- Keep a single array of the coefficient writing runs and use their
accepted output words both for the published matrix and for the bill. -/
def writeMatrixOnce {q : ℕ} (L : ℕ)
    (s : Vector (ScaledSolution (unknownCount q)) (wordCount q)) : Run (OutputMatrix q) :=
  let jobs := Vector.ofFn fun i : Fin (wordCount q) =>
    Vector.ofFn fun j : Fin (wordCount q) =>
      Vector.ofFn fun k : Fin (coefficientSlots q) =>
        emitCoefficient L ((wordIndex q).symm i) ((wordIndex q).symm j) s[i.val] k
  ⟨Vector.ofFn (fun i => Vector.ofFn (fun j => Vector.ofFn (fun k =>
      (jobs[i.val][j.val][k.val]).value))),
    16 + ∑ i : Fin (wordCount q), ∑ j : Fin (wordCount q), ∑ k : Fin (coefficientSlots q),
      ((jobs[i.val][j.val][k.val]).steps+16)⟩

theorem writeMatrixOnce_eq {q : ℕ} (L : ℕ)
    (s : Vector (ScaledSolution (unknownCount q)) (wordCount q)) :
    writeMatrixOnce L s = emitMatrix L s := by
  apply run_eq
  · apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    apply Vector.ext
    intro k hk
    simp [writeMatrixOnce,emitMatrix]
  · simp [writeMatrixOnce,emitMatrix]

def paidRow {q : ℕ} (L : ℕ) (a : Fin q → Fraction) (u : AffineEdge.Word q) :
    Run (Option (ScaledSolution (unknownCount q))) :=
  let m := equationCount q
  let n := unknownCount q
  let b := bitWidth q L
  let nav := navigation m n b
  let input := buildInputOnce a u
  let s := paidRun b nav m n (denseAugment input.value) 1
  ⟨s.value, input.steps + (m*(n+1)+1)*nav + s.steps⟩

theorem paidRow_correct {q L : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q)
    (hl : ∀ t, (a t).size ≤ L) :
    (paidRow L a u).value = (solveRow a u).result := by
  have hh : ∀ i j, ((buildTable a u).value i j).natAbs ≤ 2^generationWidth q L := by
    simpa only [buildTable_value] using generatedInt_height a u hl
  have hx : ValidTrace (bitWidth q L) (solveIntTrace (buildTable a u).value) :=
    solverTrace_bit_realizes (buildTable a u).value hh
  simpa only [paidRow,buildInputOnce_eq,solveRow,solveIntScaled] using
    paidRun_correct _ _ _ _ _ _ hx

theorem paidRow_price {q L : ℕ} (a : Fin q → Fraction) (u : AffineEdge.Word q)
    (hl : ∀ t, (a t).size ≤ L) :
    (paidRow L a u).steps ≤
      (16+equationCount q*(unknownCount q+1)*cellBudget (wordCount q) q L) +
      rowClock (equationCount q) (unknownCount q) (bitWidth q L) := by
  have hinput := buildTable_steps a u hl
  have hr := paidRun_price (bitWidth q L)
    (navigation (equationCount q) (unknownCount q) (bitWidth q L))
    (equationCount q) (unknownCount q) (denseAugment (buildTable a u).value) 1
  have hr' := hr.trans (Nat.mul_le_mul_right _
    (Nat.add_le_add_right (Nat.min_le_left _ _) 1))
  simp only [paidRow,buildInputOnce_eq,rowClock]
  omega

def rows {q : ℕ} (L : ℕ) (a : Fin q → Fraction) :
    Vector (Run (Option (ScaledSolution (unknownCount q)))) (wordCount q) :=
  Vector.ofFn fun i => paidRow L a ((wordIndex q).symm i)

def selectedSolutions {q : ℕ} (L : ℕ) (a : Fin q → Fraction) :
    Option (Vector (ScaledSolution (unknownCount q)) (wordCount q)) :=
  (rows L a).mapM (fun c => c.value)

theorem selectedSolutions_eq {q L : ℕ} (a : Fin q → Fraction)
    (hl : ∀ t, (a t).size ≤ L) : selectedSolutions L a = solveAll a := by
  have h :
      (rows L a).map Run.value =
        Vector.ofFn (fun i : Fin (wordCount q) => (solveRow a ((wordIndex q).symm i)).result) := by
    apply Vector.ext
    intro i hi
    simp only [rows,Vector.getElem_map,Vector.getElem_ofFn]
    exact paidRow_correct a _ hl
  unfold selectedSolutions solveAll
  simpa only [Vector.mapM_map,Function.comp_apply,id_eq] using
    congrArg (fun x => Vector.mapM (m := Option) id x) h

def outerDebit (D q L : ℕ) : ℕ := 32+(D+1)*(D+q+L+1)^2

/-- Actual single-output driver: generate each original row once, consume
its bit-driven elimination result, and invoke the original coefficient
writer on precisely those returned solutions. -/
def runGaussian {q : ℕ} (L : ℕ) (a : Fin q → Fraction) : Run (Option (OutputMatrix q)) :=
  let R := rows L a
  let charge := outerDebit (wordCount q) q L + ∑ i : Fin (wordCount q), R[i.val].steps
  match R.mapM (fun c => c.value) with
  | none => ⟨none,charge⟩
  | some x =>
    let e := writeMatrixOnce L x
    ⟨some e.value,charge+e.steps⟩

theorem runGaussian_output {q L : ℕ} (a : Fin q → Fraction)
    (hl : ∀ t, (a t).size ≤ L) : (runGaussian L a).value = paperOutput L a := by
  let time := outerDebit (wordCount q) q L + ∑ i : Fin (wordCount q), (rows L a)[i.val].steps
  rw [paperOutput]
  change ((match selectedSolutions L a with
    | none => ⟨none,time⟩
    | some x => ⟨some (writeMatrixOnce L x).value,time+(writeMatrixOnce L x).steps⟩)
      : AffineCost.Bit.Run (Option (OutputMatrix q))).value = _
  rw [selectedSolutions_eq a hl]
  cases solveAll a with
  | none => rfl
  | some x =>
    change some (writeMatrixOnce L x).value = some (emitMatrix L x).value
    rw [writeMatrixOnce_eq]

def maxUnknown (D q : ℕ) : ℕ := D*q + q*(2*q+3)
def widthRoof (D q L : ℕ) : ℕ :=
  let m := q*D
  2*(m*(generationWidth q L+m)+1)+maxUnknown D q+4

theorem unknown_le {q : ℕ} : unknownCount q ≤ maxUnknown (wordCount q) q := by
  unfold unknownCount measurementCount maxUnknown
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.sub_le q 2))
    (Nat.mul_le_mul_left _ (by have ht := Nat.div_le_self (q+1) 2; omega))

theorem bitWidth_le (q L : ℕ) : bitWidth q L ≤ widthRoof (wordCount q) q L := by
  unfold bitWidth traceBits minorBits widthRoof
  change 2*(min (q*wordCount q) (unknownCount q+1) *
    (generationWidth q L+min (q*wordCount q) (unknownCount q+1))+1)+unknownCount q+3+1 ≤
      2*((q*wordCount q)*(generationWidth q L+q*wordCount q)+1)+maxUnknown (wordCount q) q+4
  have hmin := Nat.min_le_left (q*wordCount q) (unknownCount q+1)
  have hb : min (q*wordCount q) (unknownCount q+1) *
      (generationWidth q L+min (q*wordCount q) (unknownCount q+1)) ≤
        (q*wordCount q)*(generationWidth q L+q*wordCount q) := by gcongr
  have hu : unknownCount q ≤ maxUnknown (wordCount q) q := unknown_le
  omega

def gaussianOutputRoof (D q L : ℕ) : ℕ :=
  let m := q*D
  16+D*D*(q+1)*(88*(m*(generationWidth q L+m)+2)^2+16)

theorem outputBudget_le (q L : ℕ) :
    outputBudget (wordCount q) q L ≤ gaussianOutputRoof (wordCount q) q L := by
  unfold outputBudget gaussianOutputRoof solutionWidth equationCount
  dsimp only
  have h : coefficientSlots q ≤ q+1 := by unfold coefficientSlots; omega
  gcongr

/-- Explicit polynomial, with the physical dimension D as a parameter. -/
def gaussianBudget (D q L : ℕ) : ℕ :=
  let m := q*D
  let n := maxUnknown D q
  let b := widthRoof D q L
  outerDebit D q L + D*(16+m*(n+1)*cellBudget D q L+rowClock m n b) + gaussianOutputRoof D q L

theorem runGaussian_price {q L : ℕ} (a : Fin q → Fraction) (hl : ∀ t, (a t).size ≤ L) :
    (runGaussian L a).steps ≤ gaussianBudget (wordCount q) q L := by
  let D := wordCount q
  let m := q*D
  let n := maxUnknown D q
  let b := widthRoof D q L
  let bound := 16+m*(n+1)*cellBudget D q L+rowClock m n b
  have hm : equationCount q = m := rfl
  have hn : unknownCount q ≤ n := unknown_le
  have hb : bitWidth q L ≤ b := bitWidth_le q L
  have hi (u : AffineEdge.Word q) : (paidRow L a u).steps ≤ bound := by
    have h₁ : 16+equationCount q*(unknownCount q+1)*cellBudget D q L ≤
        16+m*(n+1)*cellBudget D q L := by rw [hm]; gcongr
    have h₂ := rowClock_mono (le_of_eq hm) hn hb
    exact (paidRow_price a u hl).trans (Nat.add_le_add h₁ h₂)
  have hs : (∑ i : Fin D, (rows L a)[i.val].steps) ≤ D*bound := by
    calc
      _ ≤ ∑ _i : Fin D, bound := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [rows,Vector.getElem_ofFn] using hi ((wordIndex q).symm i)
      _ = _ := by simp
  let time := outerDebit D q L + ∑ i : Fin D, (rows L a)[i.val].steps
  let outBound := gaussianOutputRoof D q L
  change ((match selectedSolutions L a with
    | none => ⟨none,time⟩
    | some x => ⟨some (writeMatrixOnce L x).value,time+(writeMatrixOnce L x).steps⟩)
      : AffineCost.Bit.Run (Option (OutputMatrix q))).steps ≤ outerDebit D q L + D*bound + outBound
  have ht : time ≤ outerDebit D q L + D*bound := Nat.add_le_add_left hs _
  cases selectedSolutions L a with
  | none =>
    change time ≤ _
    exact ht.trans (Nat.le_add_right _ _)
  | some x =>
    change time+(writeMatrixOnce L x).steps ≤ _
    apply Nat.add_le_add ht
    rw [writeMatrixOnce_eq]
    exact (emitMatrix_steps (L := L) x).trans (outputBudget_le q L)

theorem original_gaussian_counted {q L : ℕ} (a : Fin q → Fraction)
    (hv : ∀ t, (a t).valid) (hl : ∀ t, (a t).size ≤ L) (hq : 2 ≤ q)
    (hi : Function.Injective (physicalLabels a)) (hn : ∀ t, physicalLabels a t ≠ 0) :
    (∃ p : OutputMatrix q, (runGaussian L a).value = some p ∧
      (∀ (i j : Fin (wordCount q)) (k : Fin (coefficientSlots q)), p[i.val][j.val][k.val].valid) ∧
      PairedCondition (physicalLabels a) (binaryEncoder q) (q-2) (outputPolynomial p)) ∧
      (runGaussian L a).steps ≤ gaussianBudget (4^q) q L := by
  refine ⟨?_, runGaussian_price a hl⟩
  rw [runGaussian_output a hl]
  exact paperOutput_spec a hv hl hq hi hn

end Paper3.BareissBit

#print axioms Paper3.BareissBit.buildInputOnce_eq
#print axioms Paper3.BareissBit.writeMatrixOnce_eq
#print axioms Paper3.BareissBit.navigation_mono
#print axioms Paper3.BareissBit.paidRow_correct
#print axioms Paper3.BareissBit.paidRow_price
#print axioms Paper3.BareissBit.selectedSolutions_eq
#print axioms Paper3.BareissBit.runGaussian_output
#print axioms Paper3.BareissBit.bitWidth_le
#print axioms Paper3.BareissBit.runGaussian_price
#print axioms Paper3.BareissBit.original_gaussian_counted

