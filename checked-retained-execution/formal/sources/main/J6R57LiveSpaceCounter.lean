import J6R15ModeCostCursor
import Mathlib.Data.Nat.Log

/-! A separately implemented bounded cumulative integer uses only its
binary word. This does not assert that the source interpreter's Nat
fields, an evaluator heap, or the proof-side level ledger are stored in
this representation. -/
namespace J6R57LiveSpace
open J6R15ModeCost
set_option autoImplicit false

def counterWidth (total : ℕ) : ℕ := Nat.clog 2 (total+1)

def cumulativeWord (total amount : ℕ) : Word (counterWidth total) := word amount

theorem cumulative_counter_has_exact_logarithmic_width {total amount : ℕ}
    (within : amount≤total) :
    (cumulativeWord total amount).val=amount ∧
      (cumulativeWord total amount).bits.length=Nat.clog 2 (total+1) := by
  have fit : amount<2^(counterWidth total) :=
    (Nat.lt_succ_of_le within).trans_le (Nat.le_pow_clog (by decide : 1<(2:ℕ)) _)
  exact ⟨word_val fit,(cumulativeWord total amount).size⟩

theorem advance_cumulative_counter_without_wrap {total amount charge : ℕ}
    (within : amount+charge≤total) :
    (cumulativeWord total (amount+charge)).val=(cumulativeWord total amount).val+charge := by
  rw [(cumulative_counter_has_exact_logarithmic_width within).1,
    (cumulative_counter_has_exact_logarithmic_width ((Nat.le_add_right amount charge).trans within)).1]

#print axioms cumulative_counter_has_exact_logarithmic_width
#print axioms advance_cumulative_counter_without_wrap
end J6R57LiveSpace
