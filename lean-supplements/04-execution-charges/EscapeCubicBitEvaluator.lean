import EscapeProductBitWork

/-! A same-input bit-cost escape: use the exact flat scan of the stored
cubic input, evaluate (I) via binary products without division, and test
the resulting signed numerator. -/

namespace RootSeparation.EscapeBits

open RootSeparation.EscapeScan RootSeparation.EscapeRational

private theorem zero_tape_iff (bits : List Bool) :
    bits.all (fun b => !b) = true ↔ decode bits = 0 := by
  induction bits with
  | nil => decide
  | cons head tail ih =>
    cases head
    · simp only [List.all_cons, Bool.not_false, Bool.true_and, ih, decode,
        Bool.toNat_false, zero_add]
      omega
    · simp [decode]

private theorem numerator_zero_iff (S : SignedProduct) :
    S.numerator.all (fun v => !v) = true ↔ S.num = 0 := by
  rw [zero_tape_iff, SignedProduct.num]
  change decode S.numerator = 0 ↔ (if S.negative then -(decode S.numerator : ℤ) else
    (decode S.numerator : ℤ)) = 0
  cases S.negative <;> simp

/-- The public size/header setup is prepaid by a quadratic bound, including
copying the flat pin tape once, reading the edge count, and computing the
two word widths. The last linear traversal tests the actual numerator bits. -/
def cubicRationalBitRun {n : ℕ} (pins : Vector Bool n) (es : List (Fin n × Fin n)) :
    Measured ℕ :=
  let m := es.length
  let aw := (max n m).log2 + 1
  let w := magnitudeWidth m
  let scan := flatScan aw pins es
  let z := bitProduct w scan.result m
  ⟨if z.result.numerator.all (fun b => !b) then 0 else 1,
    scan.steps + z.steps + n + 2 * w + 2 + 64 * (n + m + 1) ^ 2⟩

/-- Exact Eq. (I) on the same stored cubic graph, with an explicit
polynomial bound in its natural indexed bit model. No arbitrary external
solver, rational inverse, or free wide-number multiplication is used. -/
theorem literal_cubic_rational_bit_run {n : ℕ} (pins : Vector Bool n)
    (es : List (Fin n × Fin n)) (once : es.Nodup)
    (cubic : ∀ v, GraphCutMoments.degree es.toFinset v = 3) :
    (cubicRationalBitRun pins es).result = PinnedCNF.modelCount (PinnedCNF.formula es.toFinset pins.get) ∧
    (cubicRationalBitRun pins es).steps ≤ 4096 * (n + 1) ^ 4 := by
  let m := es.length
  let aw := (max n m).log2 + 1
  let w := magnitudeWidth m
  let scan := flatScan aw pins es
  let z := bitProduct w scan.result m
  have hscan : scan.result = PinnedCNF.violations es.toFinset pins.get :=
    (flat_scan_same_count_and_cost aw pins es).1.trans (indexed_scan_is_original_count pins es once).1
  have hcard : es.toFinset.card = m := List.toFinset_card_of_nodup once
  have hv : scan.result ≤ m := by
    rw [hscan, ← hcard]
    exact PinnedCNF.violations_le_card es.toFinset pins.get
  obtain ⟨_, _, hn, _, _⟩ := bit_product_contract hv (le_refl m)
  change z.result.num = (integerProduct scan.result m).1 at hn
  change (if z.result.numerator.all (fun x => !x) then 0 else 1) = _ ∧
    scan.steps + z.steps + n + 2 * w + 2 + 64 * (n + m + 1) ^ 2 ≤ _
  constructor
  · have hc := (integer_product_is_original_count es.toFinset pins.get).2
    rw [← hscan, hcard, ← hn] at hc
    rw [← hc]
    simp only [numerator_zero_iff]
  · have hm : 2 * m = 3 * n := (cubic_indexed_and_flat_work pins es once cubic).1
    have hscanCap : scan.steps + n ≤ 256 * (n + 1) ^ 3 := by
      have h := (cubic_indexed_and_flat_work pins es once cubic).2.2.1
      change scan.steps + n + 8 * (aw + 1) + 2 ≤ _ at h
      omega
    have hz : z.steps ≤ 132 * (m + 1) ^ 4 := bit_product_polynomial hv
    have hs : m + 1 ≤ 2 * (n + 1) := by omega
    have hpowers (t : ℕ) : (m + 1) ^ t ≤ 2 ^ t * (n + 1) ^ t :=
      (Nat.pow_le_pow_left hs _).trans_eq (mul_pow _ _ _)
    have hbudget (t : ℕ) (ht : t ≤ 4) : (n + 1) ^ t ≤ (n + 1) ^ 4 :=
      Nat.pow_le_pow_right (Nat.succ_pos n) ht
    have hss : scan.steps + n ≤ 256 * (n + 1) ^ 4 :=
      hscanCap.trans (Nat.mul_le_mul_left _ (hbudget 3 (by decide)))
    have hzs : z.steps ≤ 2112 * (n + 1) ^ 4 := by
      calc
        z.steps ≤ 132 * (m + 1) ^ 4 := hz
        _ ≤ 132 * (2 ^ (4 : ℕ) * (n + 1) ^ 4) := Nat.mul_le_mul_left _ (hpowers 4)
        _ = _ := by ring
    have hw : w ≤ (m + 1) ^ 2 := by
      have h := Nat.mul_le_mul_left m (Nat.add_le_add_right (Nat.log2_le_self m) 1)
      unfold w magnitudeWidth
      nlinarith only [h]
    have hwt : w ≤ 4 * (n + 1) ^ 4 := by
      apply hw.trans
      have h := (hpowers 2).trans (Nat.mul_le_mul_left _ (hbudget 2 (by decide)))
      simpa using h
    have hx : n + m + 1 ≤ 3 * (n + 1) := by omega
    have hi : (n + m + 1) ^ 2 ≤ 9 * (n + 1) ^ 4 := calc
      _ ≤ (3 * (n + 1)) ^ 2 := Nat.pow_le_pow_left hx _
      _ = 9 * (n + 1) ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hbudget 2 (by decide))
    have hpos : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos n)
    omega

#print axioms literal_cubic_rational_bit_run

end RootSeparation.EscapeBits
