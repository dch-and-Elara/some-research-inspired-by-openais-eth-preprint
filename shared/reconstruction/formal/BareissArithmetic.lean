import BareissArithmeticUnsigned
import AffineCostFraction

/-!
Signed exact division for the existing signed-word representation. The
input represents the difference of two unsigned words. The borrow pass
extracts the sign and absolute value, and every successful result has
only one possibly nonempty magnitude.
-/

namespace Reconstruction.BareissArithmetic

open AffineCost.Bit

def Canonical (a : Signed) : Prop :=
  Tight a.plus ∧ Tight a.minus ∧ (a.plus = [] ∨ a.minus = [])

private def signedValue (negative : Bool) (bits : Word) : ℤ :=
  if negative then -(value bits : ℤ) else (value bits : ℤ)

private def pack (negative : Bool) (bits : Word) : Signed :=
  if negative then ⟨[], bits⟩ else ⟨bits, []⟩

private theorem pack_number (negative : Bool) (bits : Word) :
    (pack negative bits).number = signedValue negative bits := by
  cases negative <;> simp [pack, signedValue, Signed.number]

private theorem pack_size (negative : Bool) (bits : Word) :
    (pack negative bits).size = bits.length := by
  cases negative <;> simp [pack, Signed.size]

private theorem pack_canonical (negative : Bool) {bits : Word} (h : Tight bits) :
    Canonical (pack negative bits) := by
  cases negative
  · exact ⟨h, Or.inl rfl, Or.inr rfl⟩
  · exact ⟨Or.inl rfl, h, Or.inl rfl⟩

private theorem abs_signedValue (negative : Bool) (bits : Word) :
    (signedValue negative bits).natAbs = value bits := by
  cases negative <;> simp [signedValue]

/-- Interpret both magnitude words without carrying redundant cancellation
through to the next operation. -/
private def magnitude (a : Signed) : Run (Bool × Word) :=
  let x := trialSub a.plus a.minus
  if x.value.2 then
    let y := trialSub a.minus a.plus
    ⟨(true, y.value.1), 8 + x.steps + y.steps⟩
  else ⟨(false, x.value.1), 8 + x.steps⟩

private theorem magnitude_data (a : Signed) :
    let u := (magnitude a).value
    signedValue u.1 u.2 = a.number ∧ Tight u.2 ∧ u.2.length ≤ a.size := by
  dsimp only [magnitude]
  split
  next hs =>
    have hp : value a.plus < value a.minus := (trialSub_borrow _ _).mp hs
    have hn : (trialSub a.minus a.plus).value.2 = false := by
      cases h : (trialSub a.minus a.plus).value.2
      · rfl
      · exact (not_lt_of_ge hp.le ((trialSub_borrow _ _).mp h)).elim
    have hdiff := trialSub_noBorrow hn
    have he : (value (trialSub a.minus a.plus).value.1 : ℤ) + value a.plus = value a.minus := by
      exact_mod_cast hdiff
    have hsize : (trialSub a.minus a.plus).value.1.length ≤ a.minus.length := by
      apply length_le_of_tight (trialSub_tight _ _)
      have hp := value_lt a.minus
      omega
    refine ⟨?_, trialSub_tight _ _, hsize.trans (le_max_right _ _)⟩
    simp only [signedValue, if_true, Signed.number]
    omega
  next hs =>
    have hn : (trialSub a.plus a.minus).value.2 = false := by
      cases h : (trialSub a.plus a.minus).value.2
      · rfl
      · exact (hs h).elim
    have hdiff := trialSub_noBorrow hn
    have he : (value (trialSub a.plus a.minus).value.1 : ℤ) + value a.minus = value a.plus := by
      exact_mod_cast hdiff
    have hsize : (trialSub a.plus a.minus).value.1.length ≤ a.plus.length := by
      apply length_le_of_tight (trialSub_tight _ _)
      have hp := value_lt a.plus
      omega
    refine ⟨?_, trialSub_tight _ _, hsize.trans (le_max_left _ _)⟩
    simp only [signedValue, Bool.false_eq_true, if_false, Signed.number]
    omega

private theorem magnitude_steps (a : Signed) :
    (magnitude a).steps ≤ 272 * (a.size + 1) := by
  have hp := trialSub_steps a.plus a.minus
  have hm := trialSub_steps a.minus a.plus
  have h1 : a.plus.length ≤ a.size := le_max_left _ _
  have h2 : a.minus.length ≤ a.size := le_max_right _ _
  dsimp only [magnitude]
  split <;> dsimp only <;> omega

/-- Convert a difference of words to its canonical signed representation. -/
def normalize (a : Signed) : Run Signed :=
  let r := magnitude a
  ⟨pack r.value.1 r.value.2, 8 + r.steps⟩

theorem normalize_number (a : Signed) : (normalize a).value.number = a.number := by
  simpa only [normalize, pack_number] using (magnitude_data a).1

theorem normalize_canonical (a : Signed) : Canonical (normalize a).value :=
  pack_canonical _ (magnitude_data a).2.1

theorem normalize_steps (a : Signed) : (normalize a).steps ≤ 288 * (a.size + 1) := by
  have h := magnitude_steps a
  dsimp only [normalize]
  omega

/-- Bridge from a bound on the integer's magnitude to the size of its
canonical encoding. This is useful when an external invariant bounds
values, such as the ordered-minor invariant. -/
theorem canonical_size_of_natAbs_lt {a : Signed} {B : ℕ} (hc : Canonical a)
    (hB : a.number.natAbs < 2^B) : a.size ≤ B := by
  rcases hc.2.2 with hp | hm
  · have hv : a.number.natAbs = value a.minus := by simp [Signed.number, hp]
    rw [hv] at hB
    simpa [Signed.size, hp] using length_le_of_tight hc.2.1 hB
  · have hv : a.number.natAbs = value a.plus := by simp [Signed.number, hm]
    rw [hv] at hB
    simpa [Signed.size, hm] using length_le_of_tight hc.1 hB

theorem normalize_size_of_natAbs_lt {a : Signed} {B : ℕ} (hB : a.number.natAbs < 2^B) :
    (normalize a).value.size ≤ B := by
  apply canonical_size_of_natAbs_lt (normalize_canonical a)
  rwa [normalize_number]

private theorem exists_word_of_lt_pow (B v : ℕ) (hv : v < 2^B) :
    ∃ w : Word, value w = v ∧ w.length ≤ B := by
  induction B generalizing v with
  | zero =>
    have hz : v = 0 := by simp only [pow_zero] at hv; omega
    exact ⟨[], hz.symm, by decide⟩
  | succ B ih =>
    have hquot : v / 2 < 2^B := by
      rw [pow_succ] at hv
      omega
    obtain ⟨w,hw,hl⟩ := ih (v/2) hquot
    refine ⟨decide (v % 2 = 1) :: w, ?_, by simpa using hl⟩
    have hdecomp := Nat.mod_add_div v 2
    have hrem : v % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases h : v % 2 = 1
    · simp [value_cons, digit, h, hw]
      omega
    · simp [value_cons, digit, h, hw]
      omega

/-- An abstract integer of the asserted height has a canonical encoding
of that width. This is a representation theorem. Arithmetic costs are
for the executable word routines on already encoded operands. -/
theorem exists_canonical_signed {z : ℤ} {B : ℕ} (h : z.natAbs < 2^B) :
    ∃ a : Signed, a.number = z ∧ Canonical a ∧ a.size ≤ B := by
  obtain ⟨w,hw,hsize⟩ := exists_word_of_lt_pow B z.natAbs h
  let a := pack (decide (z < 0)) (trim w).value
  refine ⟨a, ?_, pack_canonical _ (trim_tight _), ?_⟩
  · dsimp only [a]
    rw [pack_number, signedValue, trim_value, hw]
    by_cases hz : z < 0 <;> simp only [hz, decide_true, decide_false, Bool.false_eq_true,
      if_true, if_false] <;> omega
  · exact (pack_size _ _).le.trans ((trim_length _).trans hsize)

private theorem signedValue_mul_exact (a b : Bool) {xs ys q : Word}
    (h : value xs = value ys * value q) :
    signedValue b ys * signedValue (xor a b) q = signedValue a xs := by
  have h' : (value xs : ℤ) = (value ys : ℤ) * (value q : ℤ) := by exact_mod_cast h
  cases a <;> cases b <;> simp [signedValue, h']

/-- Exact signed division. It returns no value on a zero divisor or a
nonzero remainder. The two magnitude computations also handle redundant
signed inputs. -/
def exactDiv (a b : Signed) : Run (Option Signed) :=
  let x := magnitude a
  let y := magnitude b
  let q := exactDivWord x.value.2 y.value.2
  ⟨q.value.map (pack (xor x.value.1 y.value.1)), 16 + x.steps + y.steps + q.steps⟩

theorem exactDiv_result {a b q : Signed} (h : (exactDiv a b).value = some q) :
    b.number ≠ 0 ∧ b.number * q.number = a.number ∧ Canonical q ∧ q.size ≤ a.size := by
  let x := (magnitude a).value
  let y := (magnitude b).value
  let d := exactDivWord x.2 y.2
  change d.value.map (pack (xor x.1 y.1)) = some q at h
  cases hd : d.value with
  | none => simp [hd] at h
  | some w =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    rw [← h]
    have hd' := exactDivWord_sound hd
    have hx : signedValue x.1 x.2 = a.number := (magnitude_data a).1
    have hy : signedValue y.1 y.2 = b.number := (magnitude_data b).1
    have hb : b.number ≠ 0 := by
      intro hz
      have hzero : value y.2 = 0 := by rw [← abs_signedValue y.1 y.2, hy, hz, Int.natAbs_zero]
      exact (Nat.ne_of_gt hd'.1) hzero
    have hmul := signedValue_mul_exact x.1 y.1 hd'.2.1
    rw [hx, hy, ← pack_number] at hmul
    exact ⟨hb, hmul,
      pack_canonical _ hd'.2.2.1, by
        rw [pack_size]
        exact hd'.2.2.2.trans (magnitude_data a).2.2⟩

theorem exactDiv_sound {a b q : Signed} (h : (exactDiv a b).value = some q) :
    b.number ≠ 0 ∧ q.number = a.number / b.number ∧ Canonical q ∧ q.size ≤ a.size := by
  obtain ⟨hb, he, hc, hs⟩ := exactDiv_result h
  exact ⟨hb, Int.eq_ediv_of_mul_eq_right hb he, hc, hs⟩

theorem exactDiv_complete {a b : Signed} (hb : b.number ≠ 0) (hd : b.number ∣ a.number) :
    ∃ q, (exactDiv a b).value = some q := by
  let x := (magnitude a).value
  let y := (magnitude b).value
  have hx : value x.2 = a.number.natAbs := by
    rw [← abs_signedValue x.1 x.2, (magnitude_data a).1]
  have hy : value y.2 = b.number.natAbs := by
    rw [← abs_signedValue y.1 y.2, (magnitude_data b).1]
  have hp : 0 < value y.2 := by rw [hy]; exact Int.natAbs_pos.mpr hb
  have hNat : value y.2 ∣ value x.2 := by
    rw [hx, hy]
    exact Int.natAbs_dvd_natAbs.mpr hd
  obtain ⟨q,hq⟩ := exactDivWord_complete hp hNat
  refine ⟨pack (xor x.1 y.1) q, ?_⟩
  change (exactDivWord x.2 y.2).value.map (pack (xor x.1 y.1)) = _
  rw [hq, Option.map_some]

theorem exactDiv_success_iff (a b : Signed) :
    (∃ q, (exactDiv a b).value = some q) ↔ b.number ≠ 0 ∧ b.number ∣ a.number := by
  constructor
  · rintro ⟨q,hq⟩
    have h := exactDiv_result hq
    exact ⟨h.1, q.number, h.2.1.symm⟩
  · rintro ⟨hb,hd⟩
    exact exactDiv_complete hb hd

theorem exactDiv_steps (a b : Signed) :
    (exactDiv a b).steps ≤ 2048 * (a.size + b.size + 1)^2 := by
  let w := a.size + b.size + 1
  have hx := magnitude_steps a
  have hy := magnitude_steps b
  have hDiv : (exactDivWord (magnitude a).value.2 (magnitude b).value.2).steps ≤ 512*w^2 := by
    refine (exactDivWord_steps _ _).trans ?_
    have ha : (magnitude a).value.2.length + 1 ≤ w := by
      have h := (magnitude_data a).2.2
      change _ ≤ a.size + b.size + 1
      omega
    have hb : (magnitude b).value.2.length + 1 ≤ w := by
      have h := (magnitude_data b).2.2
      change _ ≤ a.size + b.size + 1
      omega
    calc
      _ ≤ (512*w)*w := Nat.mul_le_mul (Nat.mul_le_mul_left 512 ha) hb
      _ = 512*w^2 := by ring
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hw2 : w ≤ w^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  change 16 + (magnitude a).steps + (magnitude b).steps +
    (exactDivWord (magnitude a).value.2 (magnitude b).value.2).steps ≤ 2048*w^2
  simp only [w] at hw2 hDiv ⊢
  omega

/-- The existing signed adder with a sign swap on the second argument. -/
def subtract (a b : Signed) : Run Signed :=
  let d := Signed.add a b.neg
  ⟨d.value, 8 + d.steps⟩

theorem subtract_number (a b : Signed) : (subtract a b).value.number = a.number - b.number := by
  simp [subtract, sub_eq_add_neg]

theorem subtract_size (a b : Signed) : (subtract a b).value.size ≤ max a.size b.size + 1 := by
  simpa only [subtract, Signed.neg_size] using Signed.add_size a b.neg

theorem subtract_steps (a b : Signed) : (subtract a b).steps ≤ 152*(a.size+b.size+1) := by
  have H := Signed.add_steps a b.neg
  rw [Signed.neg_size] at H
  dsimp [subtract]
  omega

/-- One scalar forward Bareiss update. The underlying arithmetic calls
are two signed multiplies, one signed subtraction and one exact division.
No matrix operations are performed here. -/
def bareissUpdate (pivot entry column row previousPivot : Signed) : Run (Option Signed) :=
  let x := Signed.mul pivot entry
  let y := Signed.mul column row
  let num := subtract x.value y.value
  let r := exactDiv num.value previousPivot
  ⟨r.value, 16 + x.steps + y.steps + num.steps + r.steps⟩

theorem bareissUpdate_sound {pivot entry column row previousPivot q : Signed}
    (h : (bareissUpdate pivot entry column row previousPivot).value = some q) :
    previousPivot.number ≠ 0 ∧
      q.number = (pivot.number * entry.number - column.number * row.number) / previousPivot.number ∧
      Canonical q := by
  have hs := exactDiv_sound (a := (subtract (Signed.mul pivot entry).value
      (Signed.mul column row).value).value) (b := previousPivot) h
  exact ⟨hs.1, by
    simpa only [subtract_number, Signed.mul_number] using hs.2.1, hs.2.2.1⟩

/-- The external Bareiss invariant needs to supply divisibility of the
computed numerator. The bit program itself checks exactness. -/
theorem bareissUpdate_success_iff (pivot entry column row previousPivot : Signed) :
    (∃ q, (bareissUpdate pivot entry column row previousPivot).value = some q) ↔
      previousPivot.number ≠ 0 ∧ previousPivot.number ∣
        (pivot.number * entry.number - column.number * row.number) := by
  simpa only [bareissUpdate, subtract_number, Signed.mul_number] using
    exactDiv_success_iff (subtract (Signed.mul pivot entry).value
      (Signed.mul column row).value).value previousPivot

/-- Quadratic Boolean-cell cost for a scalar update on signed encodings
of input width at most `B`. The bound includes both products, cancellation,
and exact division. -/
theorem bareissUpdate_steps_le (pivot entry column row previousPivot : Signed) (B : ℕ)
    (h : ∀ x ∈ [pivot,entry,column,row,previousPivot], x.size ≤ B) :
    (bareissUpdate pivot entry column row previousPivot).steps ≤ 65536*(B+1)^2 := by
  let x := Signed.mul pivot entry
  let y := Signed.mul column row
  let d := subtract x.value y.value
  have hP := h pivot (by simp)
  have hE := h entry (by simp)
  have hC := h column (by simp)
  have hR := h row (by simp)
  have hD := h previousPivot (by simp)
  have hxSize : x.value.size ≤ 2*B+1 := by
    have H := Signed.mul_size pivot entry
    change (Signed.mul pivot entry).value.size ≤ _
    omega
  have hySize : y.value.size ≤ 2*B+1 := by
    have H := Signed.mul_size column row
    change (Signed.mul column row).value.size ≤ _
    omega
  have hdSize : d.value.size ≤ 2*B+2 := by
    have H := subtract_size x.value y.value
    have hM : max x.value.size y.value.size ≤ 2*B+1 := max_le hxSize hySize
    change (subtract x.value y.value).value.size ≤ _
    omega
  have mulCost (a b : Signed) (ha : a.size ≤ B) (hb : b.size ≤ B) :
      (Signed.mul a b).steps ≤ 16384*(B+1)^2 := by
    calc
      _ ≤ 4096*(a.size+b.size+1)^2 := Signed.mul_steps a b
      _ ≤ 4096*(2*(B+1))^2 := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by ring
  have hx := mulCost pivot entry hP hE
  have hy := mulCost column row hC hR
  have hsub : d.steps ≤ 608*(B+1) := by
    have H := subtract_steps x.value y.value
    change (subtract x.value y.value).steps ≤ _
    omega
  have hdiv : (exactDiv d.value previousPivot).steps ≤ 18432*(B+1)^2 := calc
    _ ≤ 2048*(d.value.size + previousPivot.size + 1)^2 := exactDiv_steps _ _
    _ ≤ 2048*(3*(B+1))^2 := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by ring
  have hB : 1 ≤ (B+1)^2 := Nat.succ_le_of_lt (by positivity)
  have hB' : B+1 ≤ (B+1)^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  change 16 + (Signed.mul pivot entry).steps + (Signed.mul column row).steps +
    d.steps + (exactDiv d.value previousPivot).steps ≤ _
  omega

/-- The same bit-cost bound with the input size supplied as an integer
height for each canonical operand. -/
theorem bareissUpdate_steps_of_height (pivot entry column row previousPivot : Signed) (B : ℕ)
    (h : ∀ x ∈ [pivot,entry,column,row,previousPivot], Canonical x ∧ x.number.natAbs < 2^B) :
    (bareissUpdate pivot entry column row previousPivot).steps ≤ 65536*(B+1)^2 :=
  bareissUpdate_steps_le pivot entry column row previousPivot B (fun x hx =>
    canonical_size_of_natAbs_lt (h x hx).1 (h x hx).2)

end Reconstruction.BareissArithmetic
