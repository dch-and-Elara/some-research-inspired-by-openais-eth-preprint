import EscapeIndexedScan
import Mathlib.Tactic.Ring

/-! Explicit binary primitive for the Section 7 escape: a one-pass ripple
adder on least-significant-bit-first lists, and multiplication by a small
integer by iteration. No multiplication of two big machine integers is
used by the executable code. -/

namespace RootSeparation.EscapeBits

open RootSeparation.EscapeScan

def decode : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * decode bs

private def gate (a b c : Bool) : Bool × Bool :=
  let x := Bool.xor a b
  (Bool.xor x c, (a && b) || (x && c))

private theorem gate_value (a b c : Bool) :
    (gate a b c).1.toNat + 2 * (gate a b c).2.toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

structure RippleResult where
  bits : List Bool
  carry : Bool
  steps : ℕ
  deriving Repr

/-- At each cell: two bit reads, five Boolean gates, and one output write.
Lengths agree on all calls in which the semantic contract is used. -/
def ripple : List Bool → List Bool → Bool → RippleResult
  | [], _, c => ⟨[], c, 1⟩
  | _ :: _, [], c => ⟨[], c, 1⟩
  | a :: as, b :: bs, c =>
    let t := gate a b c
    let r := ripple as bs t.2
    ⟨t.1 :: r.bits, r.carry, r.steps + 8⟩

theorem ripple_bit_contract (a b : List Bool) (c : Bool) (h : a.length = b.length) :
    (ripple a b c).bits.length = a.length ∧
    decode (ripple a b c).bits + 2 ^ a.length * (ripple a b c).carry.toNat =
      decode a + decode b + c.toNat ∧
    (ripple a b c).steps = 1 + 8 * a.length := by
  induction a generalizing b c with
  | nil => cases b <;> simp_all [ripple, decode]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have h' : xs.length = ys.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using h
      let t := gate x y c
      let r := ripple xs ys t.2
      obtain ⟨hlen, hv, hs⟩ := ih ys t.2 h'
      refine ⟨?_, ?_, ?_⟩
      · change r.bits.length + 1 = xs.length + 1
        exact congrArg (· + 1) hlen
      · change t.1.toNat + 2 * decode r.bits + 2 ^ (xs.length + 1) * r.carry.toNat =
          x.toNat + 2 * decode xs + (y.toNat + 2 * decode ys) + c.toNat
        calc
          _ = t.1.toNat + 2 * (decode r.bits + 2 ^ xs.length * r.carry.toNat) := by
            rw [pow_succ]
            ring
          _ = x.toNat + 2 * decode xs + (y.toNat + 2 * decode ys) + c.toNat := by
            rw [show decode r.bits + 2 ^ xs.length * r.carry.toNat =
              decode xs + decode ys + t.2.toNat from hv]
            have hg := gate_value x y c
            change t.1.toNat + 2 * t.2.toNat = _ at hg
            omega
      · change r.steps + 8 = 1 + 8 * (xs.length + 1)
        rw [show r.steps = 1 + 8 * xs.length from hs]
        omega

theorem ripple_exact_when_fits (a b : List Bool) (h : a.length = b.length)
    (fit : decode a + decode b < 2 ^ a.length) :
    (ripple a b false).bits.length = a.length ∧
    decode (ripple a b false).bits = decode a + decode b ∧
    (ripple a b false).steps = 1 + 8 * a.length := by
  obtain ⟨hl, hv, hs⟩ := ripple_bit_contract a b false h
  by_cases hc : (ripple a b false).carry
  · rw [show (ripple a b false).carry = true from hc] at hv
    simp only [Bool.toNat_true, Bool.toNat_false, mul_one, add_zero] at hv
    omega
  · have hc' : (ripple a b false).carry = false := Bool.eq_false_iff.mpr hc
    rw [hc'] at hv
    simp only [Bool.toNat_false, mul_zero, add_zero] at hv
    exact ⟨hl, hv, hs⟩

@[simp] theorem decode_zero_word (w : ℕ) : decode (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, decode, ih]

/-- The small loop counter is at most the number of stored edges. Each
iteration pays for its fixed-width decrement/zero test before using the
ripple adder. The control tariff includes list-head and carry disposal. -/
def multiplySmall (w : ℕ) (a : List Bool) : ℕ → Measured (List Bool)
  | 0 => ⟨List.replicate w false, w + 1⟩
  | k + 1 =>
    let z := multiplySmall w a k
    let r := ripple z.result a false
    ⟨r.bits, z.steps + r.steps + 8 * (w + 1)⟩

theorem multiply_small_bit_contract (w : ℕ) (a : List Bool) (h : a.length = w)
    (k : ℕ) (fit : k * decode a < 2 ^ w) :
    (multiplySmall w a k).result.length = w ∧
    decode (multiplySmall w a k).result = k * decode a ∧
    (multiplySmall w a k).steps = w + 1 + k * (1 + 8 * w + 8 * (w + 1)) := by
  induction k with
  | zero => simp [multiplySmall]
  | succ k ih =>
    have prefit : k * decode a < 2 ^ w :=
      (Nat.mul_le_mul_right _ (Nat.le_succ k)).trans_lt fit
    obtain ⟨hl, hv, hs⟩ := ih prefit
    let z := multiplySmall w a k
    have fa : decode z.result + decode a < 2 ^ z.result.length := by
      change decode (multiplySmall w a k).result + decode a <
        2 ^ (multiplySmall w a k).result.length
      rw [hv, hl, ← Nat.succ_mul]
      exact fit
    obtain ⟨h'len, h'decode, h'steps⟩ := ripple_exact_when_fits z.result a (hl.trans h.symm) fa
    change (ripple z.result a false).bits.length = w ∧
      decode (ripple z.result a false).bits = (k + 1) * decode a ∧
      z.steps + (ripple z.result a false).steps + 8 * (w + 1) =
        w + 1 + (k + 1) * (1 + 8 * w + 8 * (w + 1))
    refine ⟨h'len.trans hl, ?_, ?_⟩
    · exact h'decode.trans (by rw [show decode z.result = k * decode a from hv, Nat.succ_mul])
    · rw [h'steps, show z.steps = _ from hs, show z.result.length = w from hl]
      ring

#print axioms ripple_bit_contract
#print axioms ripple_exact_when_fits
#print axioms decode_zero_word
#print axioms multiply_small_bit_contract

end RootSeparation.EscapeBits
