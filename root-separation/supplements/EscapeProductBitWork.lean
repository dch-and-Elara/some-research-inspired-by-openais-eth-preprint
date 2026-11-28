import EscapeRipple
import EscapeRationalProduct
import Mathlib.Tactic.Linarith

/-! The actual cleared-denominator evaluation of (I) using fixed binary
lists and the verified ripple primitive. Small signed differences and loop
control have explicit conservative fixed-width bit tariffs. -/

namespace RootSeparation.EscapeBits

open RootSeparation.EscapeScan RootSeparation.EscapeRational

structure SignedProduct where
  negative : Bool
  numerator : List Bool
  denominator : List Bool
  deriving Repr

private def withSign (b : Bool) (v : ℕ) : ℤ :=
  if b then -(v : ℤ) else (v : ℤ)

def SignedProduct.num (p : SignedProduct) : ℤ := withSign p.negative (decode p.numerator)

def SignedProduct.den (p : SignedProduct) : ℕ := decode p.denominator

private theorem with_sign_abs (b : Bool) (v : ℕ) : (withSign b v).natAbs = v := by
  cases b <;> simp [withSign]

private theorem with_sign_restore (x : ℤ) : withSign (decide (x < 0)) x.natAbs = x := by
  unfold withSign
  by_cases hx : x < 0
  · simp only [decide_eq_true_eq, if_pos hx]
    omega
  · simp only [decide_eq_true_eq, if_neg hx]
    omega

private theorem with_sign_mul (b c : Bool) (u v : ℕ) :
    withSign (Bool.xor b c) (u * v) = withSign b u * withSign c v := by
  cases b <;> cases c <;> simp [withSign]

private def oneWord : ℕ → List Bool
  | 0 => []
  | k + 1 => true :: List.replicate k false

private theorem one_length (w : ℕ) : (oneWord w).length = w := by
  cases w <;> simp [oneWord]

private theorem one_value (w : ℕ) (hw : 0 < w) : decode (oneWord w) = 1 := by
  cases w with
  | zero => simp at hw
  | succ w => simp [oneWord, decode]

/-- Actual binary prefix-product evaluator. The only multiplications of a
wide word are calls to the bit-level repeated-addition routine. At index
`j+1` the auxiliary subtraction compares small indices of the same
width; the tariff also pays the sign operation, loop control and copies. -/
def bitProduct (w v : ℕ) : ℕ → Measured SignedProduct
  | 0 => ⟨⟨false, oneWord w, oneWord w⟩, 2 * w + 2⟩
  | j + 1 =>
    let z := bitProduct w v j
    let factor : ℤ := (j + 1 : ℕ) - (v : ℤ)
    let a := multiplySmall w z.result.numerator factor.natAbs
    let b := multiplySmall w z.result.denominator (j + 1)
    ⟨⟨Bool.xor z.result.negative (decide (factor < 0)), a.result, b.result⟩,
      z.steps + a.steps + b.steps + 24 * (w + 1)⟩

private theorem scale_call_upper (w : ℕ) (src : List Bool) (hsrc : src.length = w)
    (k m : ℕ) (hk : k ≤ m) (fit : k * decode src < 2 ^ w) :
    (multiplySmall w src k).steps ≤ 18 * (m + 1) * (w + 1) := by
  rw [(multiply_small_bit_contract w src hsrc k fit).2.2]
  have hu : 1 + 8 * w + 8 * (w + 1) ≤ 17 * (w + 1) := by omega
  calc
    _ ≤ w + 1 + m * (17 * (w + 1)) := Nat.add_le_add_left (Nat.mul_le_mul hk hu) _
    _ = (1 + 17 * m) * (w + 1) := by ring
    _ ≤ 18 * (m + 1) * (w + 1) := Nat.mul_le_mul_right _ (by omega)

/-- Every real prefix has the indicated width and exact integer value. The
constant in the time bound accommodates every iteration of both additions. -/
theorem bit_product_contract {v m : ℕ} (hv : v ≤ m) {j : ℕ} (hj : j ≤ m) :
    let w := magnitudeWidth m
    let z := bitProduct w v j
    z.result.numerator.length = w ∧ z.result.denominator.length = w ∧
      z.result.num = (integerProduct v j).1 ∧
      z.result.den = (integerProduct v j).2 ∧
      z.steps ≤ 2 * w + 2 + j * (64 * (m + 1) * (w + 1)) := by
  let w := magnitudeWidth m
  change (bitProduct w v j).result.numerator.length = w ∧
    (bitProduct w v j).result.denominator.length = w ∧
    (bitProduct w v j).result.num = (integerProduct v j).1 ∧
    (bitProduct w v j).result.den = (integerProduct v j).2 ∧
    (bitProduct w v j).steps ≤ 2 * w + 2 + j * (64 * (m + 1) * (w + 1))
  have hw : 0 < w := by unfold w magnitudeWidth; omega
  induction j with
  | zero =>
    simp [bitProduct, integerProduct, SignedProduct.num, SignedProduct.den, withSign,
      one_length, one_value w hw]
  | succ j ih =>
    let z := bitProduct w v j
    let d : ℤ := (j + 1 : ℕ) - (v : ℤ)
    let a := multiplySmall w z.result.numerator d.natAbs
    let b := multiplySmall w z.result.denominator (j + 1)
    obtain ⟨hna, hnb, hnaVal, hnbVal, hz⟩ := ih (Nat.le_of_succ_le hj)
    have hmaga : decode z.result.numerator = (integerProduct v j).1.natAbs :=
      (with_sign_abs _ _).symm.trans (congrArg Int.natAbs hnaVal)
    have hmagb : decode z.result.denominator = (integerProduct v j).2 := hnbVal
    obtain ⟨hfitA, hfitB⟩ := integer_product_prefix_width hv hj
    have fa : d.natAbs * decode z.result.numerator < 2 ^ w := by
      simpa only [hmaga, Nat.mul_comm d.natAbs, integerProduct, Int.natAbs_mul] using hfitA
    have fb : (j + 1) * decode z.result.denominator < 2 ^ w := by
      simpa only [hmagb, Nat.mul_comm (j + 1), integerProduct] using hfitB
    obtain ⟨hla, hva, _⟩ := multiply_small_bit_contract w z.result.numerator hna d.natAbs fa
    obtain ⟨hlb, hvb, _⟩ := multiply_small_bit_contract w z.result.denominator hnb (j + 1) fb
    change a.result.length = w ∧ b.result.length = w ∧
      withSign (Bool.xor z.result.negative (decide (d < 0))) (decode a.result) =
        (integerProduct v j).1 * d ∧
      decode b.result = (integerProduct v j).2 * (j + 1) ∧
      z.steps + a.steps + b.steps + 24 * (w + 1) ≤
        2 * w + 2 + (j + 1) * (64 * (m + 1) * (w + 1))
    refine ⟨hla, hlb, ?_, ?_, ?_⟩
    · rw [show decode a.result = d.natAbs * decode z.result.numerator from hva,
        Nat.mul_comm d.natAbs, with_sign_mul, with_sign_restore]
      exact congrArg (· * d) hnaVal
    · exact hvb.trans (by rw [hmagb, Nat.mul_comm])
    · have hd : d.natAbs ≤ m := by unfold d; omega
      have ha : a.steps ≤ 18 * (m + 1) * (w + 1) :=
        scale_call_upper w z.result.numerator hna d.natAbs m hd fa
      have hb : b.steps ≤ 18 * (m + 1) * (w + 1) :=
        scale_call_upper w z.result.denominator hnb (j + 1) m hj fb
      have hc : w + 1 ≤ (m + 1) * (w + 1) := by
        simpa only [one_mul] using Nat.mul_le_mul_right (w + 1) (show 1 ≤ m + 1 by omega)
      have hz' : z.steps ≤ 2 * w + 2 + j * (64 * (m + 1) * (w + 1)) := hz
      simp only [Nat.succ_mul]
      nlinarith only [ha, hb, hc, hz']

/-- The polynomial factor is independent of the signs and precise counts. -/
theorem bit_product_polynomial {v m : ℕ} (hv : v ≤ m) :
    (bitProduct (magnitudeWidth m) v m).steps ≤ 132 * (m + 1) ^ 4 := by
  let w := magnitudeWidth m
  have hw : w + 1 ≤ 2 * (m + 1) ^ 2 := by
    have h := Nat.mul_le_mul_left m (Nat.add_le_add_right (Nat.log2_le_self m) 1)
    unfold w magnitudeWidth
    nlinarith only [h]
  have h := (bit_product_contract hv (le_refl m)).2.2.2.2
  change _ ≤ 2 * w + 2 + m * (64 * (m + 1) * (w + 1)) at h
  apply h.trans
  calc
    _ = (2 + 64 * m * (m + 1)) * (w + 1) := by ring
    _ ≤ (66 * (m + 1) ^ 2) * (2 * (m + 1) ^ 2) :=
      Nat.mul_le_mul (by nlinarith) hw
    _ = _ := by ring

#print axioms bit_product_contract
#print axioms bit_product_polynomial

end RootSeparation.EscapeBits
