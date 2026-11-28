import J6NativeHeightClearing
import J6Recovery

/-! Integer normalization for the J6 layer recovery. This part does not
assume that any recursive implementation returns the expected register. -/
namespace J6IntegerLayers
open scoped BigOperators Polynomial
open Polynomial J6NativeHeight
variable {P T : Type*} [Fintype P] [DecidableEq P] [Fintype T] [DecidableEq T]

/-- A padding column contributes one equality bit, shared across both of
its unary port occurrences. The case k = 2 is not two independent bits. -/
def pad (n d : ℤ) (k : ℕ) : ℤ :=
  d^2 + d^(2-k)*(d-n)^k

set_option linter.unnecessarySeqFocus false in
theorem pad_cast (n d : ℤ) (hd : d ≠ 0) (k : ℕ) (hk : k ≤ 2) :
    (pad n d k : ℚ) = (d:ℚ)^2 * (1 + (1 - (n:ℚ)/d)^k) := by
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd
  interval_cases k <;> unfold pad <;> push_cast <;>
    norm_num <;> field_simp <;> ring

theorem pad_pos (n d : ℤ) (hd : 0 < d) (hn : n ≤ 0) (k : ℕ) :
    0 < pad n d k := by
  unfold pad
  exact add_pos_of_pos_of_nonneg (pow_pos hd _) (mul_nonneg (pow_nonneg hd.le _) (pow_nonneg (by omega) _))

theorem pad_shared_bit (n d : ℤ) (k : ℕ) (hk : k ≤ 2) :
    (∑ x : Bool, d^(2-k) * (if x then d-n else d)^k) = pad n d k := by
  simp [pad,← pow_add,Nat.sub_add_cancel hk,add_comm]

def oldLayer (A B : (P → Bool) → Bool) (n d : ℤ) : ℤ :=
  ∑ y : P → Bool, ∑ x : P → Bool,
    if A y && B x then ∏ j, entry n d (y j) (x j) else 0

def oldWeight (a : (P → Bool) → Bool) (y : P → Bool) : ℚ :=
  if a y then 1 else 0

theorem oldLayer_cast (A B : (P → Bool) → Bool) (n d : ℤ) (hd : d ≠ 0) :
    (oldLayer A B n d : ℚ) = (d:ℚ)^Fintype.card P *
      (LayerRecovery.layerPolynomial (oldWeight A) (oldWeight B)).eval ((n:ℚ)/d) := by
  classical
  have h := J6NativeHeightClearing.explicit_cleared_numerator A B (fun j x => x j) n d hd
  rw [LayerRecovery.layerPolynomial_eval]
  rw [show oldLayer A B n d = numerator A B (fun j x => x j) n d from rfl, h]
  congr 1
  unfold J6NativeHeightClearing.rationalSlot
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  cases ha : A y <;> cases hb : B x <;>
    simp [ha,hb,oldWeight]
  apply Finset.prod_congr rfl
  intro j _
  cases (y j) <;> cases (x j) <;> simp [LayerRecovery.wireFactor]

/-- The factor multiplier is an integer. Recovering an odd root after
division by this multiplier takes place in the integers. -/
def factor (n d : ℤ) (t q : ℕ) (k : T → ℕ) : ℤ :=
  d^(t*Fintype.card P) * 2^(q*t) * ∏ v, pad n d (k v)

omit [DecidableEq T] [DecidableEq P] in
theorem public_pos (n d : ℤ) (t q : ℕ) (k : T → ℕ) (hd : 0 < d) (hn : n ≤ 0) :
    0 < factor (P:=P) n d t q k := by
  unfold factor
  exact mul_pos (mul_pos (pow_pos hd _) (pow_pos (by norm_num) _))
    (Finset.prod_pos fun v _ => pad_pos n d hd hn (k v))

omit [DecidableEq T] [DecidableEq P] in
theorem public_cast (n d : ℤ) (t q : ℕ) (k : T → ℕ) (hd : d ≠ 0)
    (hk : ∀ v, k v ≤ 2) :
    (factor (P:=P) n d t q k : ℚ) =
      (d:ℚ)^(t*Fintype.card P + 2*Fintype.card T) *
      ((2:ℚ)^(q*t) * ∏ v, (1+(1-(n:ℚ)/d)^(k v))) := by
  unfold factor
  push_cast
  simp only [pad_cast n d hd _ (hk _),Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  rw [pow_add, pow_mul (d:ℚ) 2]
  ring

omit [DecidableEq T] in
theorem integer_factorization (A B : (P → Bool) → Bool) (n d : ℤ) (t q e : ℕ)
    (k : T → ℕ) (hd : d ≠ 0) (hk : ∀ v, k v ≤ 2) :
    ((factor (P:=P) n d t q k * (oldLayer A B n d)^e : ℤ) : ℚ) =
    (d:ℚ)^((t+e)*Fintype.card P + 2*Fintype.card T) *
      (((2:ℚ)^(q*t) * ∏ v, (1+(1-(n:ℚ)/d)^(k v))) *
       ((LayerRecovery.layerPolynomial (oldWeight A) (oldWeight B)).eval ((n:ℚ)/d))^e) := by
  push_cast
  rw [public_cast n d t q k hd hk,oldLayer_cast A B n d hd,mul_pow,← pow_mul,Nat.add_mul]
  rw [pow_add, pow_add, pow_add]
  ring

theorem integer_root_unique (a b u : ℤ) (e : ℕ) (hu : u ≠ 0) (he : Odd e)
    (h : u*a^e = u*b^e) : a = b := by
  exact (he.strictMono_pow (R:=ℤ)).injective (mul_left_cancel₀ hu h)

#print axioms pad_cast
#print axioms pad_shared_bit
#print axioms pad_pos
#print axioms oldLayer_cast
#print axioms public_pos
#print axioms public_cast
#print axioms integer_factorization
#print axioms integer_root_unique
end J6IntegerLayers