import PinnedCNF
import GraphCutMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The first escape in Section 7, on a resident pin array and an ordered
list of stored edge records. Counters below specify the indexed-word model
and an explicit flat scan with conservative fixed-width bit tariffs. -/

namespace RootSeparation.EscapeScan

open scoped BigOperators

structure Measured (A : Type) where
  result : A
  steps : ℕ
  deriving Repr

private def bad (a b : Bool) : ℕ := (!a && !b).toNat

private theorem bad_eq (a b : Bool) : bad a b = (1 - a.toNat) * (1 - b.toNat) := by
  cases a <;> cases b <;> decide

/-- An indexed-word scan counts every edge, including edges with both pins
true; no early termination or extra representation is used. An iteration
has two endpoint loads, two pin reads, two NOTs, one AND, one accumulator
addition, and two list traversal operations. -/
def wordScan {n : ℕ} (pins : Vector Bool n) :
    List (Fin n × Fin n) → Measured ℕ
  | [] => ⟨0, 1⟩
  | e :: es =>
    let a := pins.get e.1
    let b := pins.get e.2
    let r := wordScan pins es
    ⟨bad a b + r.result, r.steps + 10⟩

theorem word_scan_exact {n : ℕ} (pins : Vector Bool n) (es : List (Fin n × Fin n)) :
    (wordScan pins es).result = (es.map fun e => bad (pins.get e.1) (pins.get e.2)).sum ∧
    (wordScan pins es).steps = 1 + 10 * es.length := by
  induction es with
  | nil => simp [wordScan]
  | cons e es ih =>
    simp only [wordScan, List.map_cons, List.sum_cons, List.length_cons, ih.1, true_and, ih.2]
    omega

/-- Sequential pin lookup for the bit model, with a decrementing binary
address of known width. Per visited cell the tariff pays fixed-width zero
test and decrement, and the bit-cell read and head move. -/
def flatRead (w : ℕ) : List Bool → ℕ → Measured Bool
  | [], _ => ⟨false, 2⟩
  | a :: _, 0 => ⟨a, 2 + 8 * (w + 1)⟩
  | _ :: as, i + 1 =>
    let r := flatRead w as i
    ⟨r.result, r.steps + 8 * (w + 1)⟩

theorem flat_read_exact (w : ℕ) (as : List Bool) (i : ℕ) (h : i < as.length) :
    (flatRead w as i).result = as[i] ∧
    (flatRead w as i).steps = 2 + (i + 1) * (8 * (w + 1)) := by
  induction as generalizing i with
  | nil => simp at h
  | cons a as ih =>
    cases i with
    | zero => simp [flatRead]
    | succ i =>
      have h' : i < as.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using h
      obtain ⟨hv, hf⟩ := ih i h'
      simp only [flatRead, List.getElem_cons_succ, hv, hf, true_and]
      ring

/-- The same scan on a flat copy of the pin tape. The control and addition
charge pays fixed-width carry propagation, rather than treating addition
as one bit operation. -/
private def flatScanTape {n : ℕ} (w : ℕ) (tape : List Bool) :
    List (Fin n × Fin n) → Measured ℕ
  | [] => ⟨0, 1⟩
  | e :: es =>
    let a := flatRead w tape e.1.val
    let b := flatRead w tape e.2.val
    let r := flatScanTape w tape es
    ⟨bad a.result b.result + r.result, r.steps + a.steps + b.steps + 16 * (w + 1)⟩

def flatScan {n : ℕ} (w : ℕ) (pins : Vector Bool n) (es : List (Fin n × Fin n)) :
    Measured ℕ :=
  flatScanTape w pins.toList es

private theorem flat_pin (w : ℕ) {n : ℕ} (pins : Vector Bool n) (i : Fin n) :
    (flatRead w pins.toList i.val).result = pins.get i ∧
    (flatRead w pins.toList i.val).steps ≤ 2 + n * (8 * (w + 1)) := by
  have hi : i.val < pins.toList.length := by simpa only [Vector.length_toList] using i.isLt
  obtain ⟨hv, hf⟩ := flat_read_exact w pins.toList i.val hi
  refine ⟨?_, ?_⟩
  · simpa using hv
  · rw [hf]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt)) _

theorem flat_scan_same_count_and_cost {n : ℕ} (w : ℕ) (pins : Vector Bool n)
    (es : List (Fin n × Fin n)) :
    (flatScan w pins es).result = (wordScan pins es).result ∧
    (flatScan w pins es).steps ≤ 1 + es.length * (4 + 16 * ((n + 1) * (w + 1))) := by
  induction es with
  | nil => simp [flatScan, flatScanTape, wordScan]
  | cons e es ih =>
    obtain ⟨ha, hfa⟩ := flat_pin w pins e.1
    obtain ⟨hb, hfb⟩ := flat_pin w pins e.2
    constructor
    · change bad (flatRead w pins.toList e.1.val).result (flatRead w pins.toList e.2.val).result +
          (flatScan w pins es).result = bad (pins.get e.1) (pins.get e.2) + (wordScan pins es).result
      rw [ha, hb, ih.1]
    · simp only [flatScan, flatScanTape, List.length_cons]
      calc
        _ ≤ (1 + es.length * (4 + 16 * ((n + 1) * (w + 1)))) +
            (2 + n * (8 * (w + 1))) + (2 + n * (8 * (w + 1))) + 16 * (w + 1) :=
          Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add ih.2 hfa) hfb) _
        _ = _ := by ring

theorem word_scan_count_le_length {n : ℕ} (pins : Vector Bool n)
    (es : List (Fin n × Fin n)) : (wordScan pins es).result ≤ es.length := by
  induction es with
  | nil => simp [wordScan]
  | cons e es ih =>
    have hb : bad (pins.get e.1) (pins.get e.2) ≤ 1 := by
      have shape : ∀ x y : Bool, bad x y ≤ 1 := by
        intro x y
        cases x <;> cases y <;> decide
      exact shape _ _
    simp only [wordScan, List.length_cons]
    omega

/-- All addresses, the public list size and every suffix accumulator fit the
same binary width used in the flat-scan tariff. -/
theorem flat_address_and_accumulator_fit {n : ℕ} (pins : Vector Bool n)
    (es : List (Fin n × Fin n)) :
    let w := (max n es.length).log2 + 1
    n < 2 ^ w ∧ es.length < 2 ^ w ∧
    ∀ k, (flatScan w pins (es.drop k)).result < 2 ^ w := by
  intro w
  have hw : max n es.length < 2 ^ w := Nat.lt_log2_self
  refine ⟨(le_max_left _ _).trans_lt hw, (le_max_right _ _).trans_lt hw, ?_⟩
  intro k
  rw [(flat_scan_same_count_and_cost w pins (es.drop k)).1]
  apply (word_scan_count_le_length pins (es.drop k)).trans_lt
  have hm : (es.drop k).length ≤ es.length := by
    rw [List.length_drop]
    exact Nat.sub_le _ _
  exact hm.trans_lt ((le_max_right _ _).trans_lt hw)

/-- The graph records occur once. The scan therefore reads the exact statistic
in (I), not just a Boolean OR surrogate. The final global zero test is exact. -/
theorem indexed_scan_is_original_count {n : ℕ} (pins : Vector Bool n)
    (es : List (Fin n × Fin n)) (once : es.Nodup) :
    (wordScan pins es).result = PinnedCNF.violations es.toFinset pins.get ∧
    (if (wordScan pins es).result = 0 then 1 else 0) =
      PinnedCNF.modelCount (PinnedCNF.formula es.toFinset pins.get) := by
  have h := (word_scan_exact pins es).1
  have hv : (wordScan pins es).result = PinnedCNF.violations es.toFinset pins.get := by
    rw [h, PinnedCNF.violations, ← List.sum_toFinset (fun e => bad (pins.get e.1) (pins.get e.2)) once]
    simp_rw [bad_eq]
  exact ⟨hv, by rw [hv, PinnedCNF.count_by_zero_test]⟩

/-- In the natural address/counter width, the linear indexed-word execution
and polynomial flat bit tariff apply to the same cubic input. The additive
terms pay pin tape setup and one final zero test on the fixed-width counter. -/
theorem cubic_indexed_and_flat_work {n : ℕ} (pins : Vector Bool n)
    (es : List (Fin n × Fin n)) (once : es.Nodup)
    (cubic : ∀ v, GraphCutMoments.degree es.toFinset v = 3) :
    let w := (max n es.length).log2 + 1
    let m := es.length
    2 * m = 3 * n ∧
    (wordScan pins es).steps + n + 2 ≤ 17 * n + 3 ∧
    (flatScan w pins es).steps + n + 8 * (w + 1) + 2 ≤ 256 * (n + 1) ^ 3 ∧
    (if (flatScan w pins es).result = 0 then 1 else 0) =
      PinnedCNF.modelCount (PinnedCNF.formula es.toFinset pins.get) := by
  intro w m
  have card := List.toFinset_card_of_nodup once
  have hm := GraphCutMoments.regular_edge_count es.toFinset 3 cubic
  rw [card, Fintype.card_fin] at hm
  have hm2 : m ≤ 2 * n := by dsimp only [m]; omega
  have hw : w + 1 ≤ 2 * (n + 1) := by
    have ht : max n es.length ≤ 2 * n := max_le (by omega) hm2
    have hl := Nat.log2_le_self (max n es.length)
    dsimp only [w]
    omega
  have hs := (flat_scan_same_count_and_cost w pins es).2
  have ht := Nat.mul_le_mul_left (n + 1) hw
  refine ⟨hm, ?_, ?_, ?_⟩
  · rw [(word_scan_exact pins es).2]
    omega
  · change _ + n + 8 * (w + 1) + 2 ≤ _
    have hz : m * (4 + 16 * ((n + 1) * (w + 1))) ≤
        (2 * n) * (4 + 16 * ((n + 1) * (2 * (n + 1)))) :=
      Nat.mul_le_mul hm2 (Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _)
    change _ ≤ 1 + m * (4 + 16 * ((n + 1) * (w + 1))) at hs
    have hb := Nat.mul_le_mul_left 8 hw
    nlinarith only [hs, hz, hb]
  · rw [(flat_scan_same_count_and_cost w pins es).1]
    exact (indexed_scan_is_original_count pins es once).2

#print axioms word_scan_exact
#print axioms flat_read_exact
#print axioms flat_scan_same_count_and_cost
#print axioms word_scan_count_le_length
#print axioms flat_address_and_accumulator_fit
#print axioms indexed_scan_is_original_count
#print axioms cubic_indexed_and_flat_work

end RootSeparation.EscapeScan
