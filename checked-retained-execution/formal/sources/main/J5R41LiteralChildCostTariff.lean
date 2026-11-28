import J5R41LiteralChildCostWork
import J5R41LiteralChildCostAlgebra
import Mathlib.Data.Nat.Bits

/-! Explicit arithmetic counts for the literal gather and each new tuple.
The purpose of addressTape is to keep dense address handling/accounting
separate from arithmetic, not to assume pre-existing tuple replies. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

theorem digit_exponent_append (x y : List Bool) (n : ℕ) :
    J45Cost.digitExponent (x++y) n = J45Cost.digitExponent y (J45Cost.digitExponent x n) := by
  induction x generalizing n with
  | nil => rfl
  | cons b bs ih =>
    simpa only [List.cons_append,J45Cost.digitExponent] using (ih (n+n+(if b then 1 else 0)))

theorem canonical_digits_exponent (n : ℕ) : J45Cost.digitExponent n.bits.reverse 0=n := by
  induction n using Nat.binaryRec' with
  | zero => simp [J45Cost.digitExponent]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h,List.reverse_cons,digit_exponent_append,ih]
    cases b <;> simp [J45Cost.digitExponent,Nat.bit_val] <;> omega

theorem canonical_digits_len (n : ℕ) : n.bits.reverse.length≤n := by
  rw [List.length_reverse]
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h,List.length_cons,Nat.bit_val]
    cases b
    · have hn : n≠0 := by intro e; exact Bool.false_ne_true (h e)
      simp only [Bool.toNat_false,Nat.zero_add]
      omega
    · simp only [Bool.toNat_true]
      omega

theorem native_digit_power {R : Type*} [Monoid R] (x : R) (n : ℕ) :
    J45Cost.digitPower x n.bits.reverse 1=x^n := by
  rw [←pow_zero x,J45Cost.digitPower_exact,canonical_digits_exponent]

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G)
variable {p : ℕ} (req : Finset (Mode i p P.mask))

theorem actual_gather_ring_fee (t : ℤ) (degree e addressTape : ℕ)
    (hd : ∀ b : B,Nat.card (ParentPorts N (.inr b))≤degree) :
    Nat.card (GatherVisits P i g req t)*J45Cost.gatherTariff e p addressTape ≤
      (2^(matched P i g t).card*V P i req*(Fintype.card B*2^degree)) *
        (21*(e+1)^2*(p+1)^2+addressTape) :=
  Nat.mul_le_mul (literal_full_gather_bound P i g req t degree hd)
    (J45Cost.gatherTariff_le e p addressTape)

theorem actual_parity_gather_bound (t : ℤ) (degree : ℕ)
    (hd : ∀ b : B,Nat.card (ParentPorts N (.inr b))≤degree) :
    Nat.card (ParityVisits P i g t)≤
      2^((matched P i g t).card+Nat.card (Tile P i×Bool))*(Fintype.card B*2^degree) := by
  rw [literal_parity_gather_count]
  exact Nat.mul_le_mul_left _ (local_column_degree_count P i g degree hd)

/-- One per-coordinate factor multiplied into the product plus one ring
multiplication per box address by the stored coefficient. These are the
only multiplications apart from binary exponentiation for a single reply. -/
theorem literal_tuple_multiplication_bound (β : LegalTuple P i p) :
    V P i req*(1+∑ m∈req,(J45Cost.digitMultiplications (β.val m).bits.reverse+1)) ≤
      V P i req*(1+req.card*(2*p+1)) := by
  have d (m : Mode i p P.mask) : J45Cost.digitMultiplications (β.val m).bits.reverse+1≤2*p+1 := by
    have h := (J45Cost.digitMultiplications_le (β.val m).bits.reverse).trans
      (Nat.mul_le_mul_left _ ((canonical_digits_len _).trans (Nat.le_of_lt (legal_exponent_small P i p β m))))
    omega
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_left
  exact (Finset.sum_le_sum (fun m hm=>d m)).trans (by simp)

#print axioms digit_exponent_append
#print axioms canonical_digits_exponent
#print axioms canonical_digits_len
#print axioms native_digit_power
#print axioms actual_gather_ring_fee
#print axioms actual_parity_gather_bound
#print axioms literal_tuple_multiplication_bound
end
end J5R41LiteralChildCost

