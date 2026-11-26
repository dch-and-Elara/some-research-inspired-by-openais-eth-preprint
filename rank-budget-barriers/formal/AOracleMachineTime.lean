import AOracleSuccinctCost
import Mathlib.Tactic

/-!
# Metered bit operations for the compact A1 verifier

Little-endian tapes have explicit bitwise carry, equality and ordering
updates. Costs count elementary Boolean gates and bit reads/writes
according to the declared local gate envelopes. There is no use of
unbounded word arithmetic in the executable loops.
-/

namespace AOracleMachineTime

structure Meter (α : Type*) where
  result : α
  steps : ℕ

def Meter.pure {α : Type*} (x : α) : Meter α := ⟨x,0⟩

def Meter.bind {α β : Type*} (x : Meter α) (f : α → Meter β) : Meter β :=
  let y := f x.result
  ⟨y.result,x.steps+y.steps⟩

def bitsValue : List Bool → ℕ
  | [] => 0
  | a :: xs => a.toNat + 2*bitsValue xs

theorem bitsValue_lt (xs : List Bool) : bitsValue xs < 2^xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    have h : b.toNat ≤ 1 := by cases b <;> decide
    simp only [bitsValue, List.length_cons, pow_succ]
    omega

/-- Least significant first. The two Boolean circuits below have
bounded gate count, independent of the tape length or values. -/
def sumBit (a b carry : Bool) : Bool := (a != b) != carry

def carryBit (a b carry : Bool) : Bool := (a && b) || ((a || b) && carry)

theorem full_adder (a b c : Bool) :
    (sumBit a b c).toNat+2*(carryBit a b c).toNat = a.toNat+b.toNat+c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

def addCore (carry : Bool) : List (Bool × Bool) → Meter (List Bool × Bool)
  | [] => ⟨([],carry),0⟩
  | (a,b) :: xs =>
    let tail := addCore (carryBit a b carry) xs
    ⟨(sumBit a b carry :: tail.result.1,tail.result.2),tail.steps+12⟩

theorem addCore_shape (carry : Bool) (xs : List (Bool × Bool)) :
    (addCore carry xs).result.1.length = xs.length ∧
      (addCore carry xs).steps = 12*xs.length := by
  induction xs generalizing carry with
  | nil => exact ⟨rfl,rfl⟩
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    obtain ⟨h1,h2⟩ := ih (carryBit a b carry)
    constructor
    · change (addCore (carryBit a b carry) xs).result.1.length+1=xs.length+1
      rw [h1]
    · change (addCore (carryBit a b carry) xs).steps+12=12*(xs.length+1)
      rw [h2, Nat.mul_succ]

theorem addCore_exact (carry : Bool) (xs : List (Bool × Bool)) :
    bitsValue (addCore carry xs).result.1 +
      2^xs.length*(addCore carry xs).result.2.toNat =
      bitsValue (xs.map Prod.fst)+bitsValue (xs.map Prod.snd)+carry.toNat := by
  induction xs generalizing carry with
  | nil => simp [addCore, bitsValue]
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    have hh := ih (carryBit a b carry)
    have hc := full_adder a b carry
    simp only [addCore, List.length_cons, List.map_cons, bitsValue, pow_succ]
    nlinarith

/-- Compare two equal-width tapes by their highest unequal bit. Local
steps carry both equality and ordered state; no hardware integer
comparison is used. -/
def orderCore : List (Bool × Bool) → Meter (Bool × Bool)
  | [] => ⟨(false,true),0⟩
  | (a,b) :: xs =>
    let high := orderCore xs
    ⟨(high.result.1 || (high.result.2 && !a && b),
      high.result.2 && (a == b)),high.steps+10⟩

theorem orderCore_exact (xs : List (Bool × Bool)) :
    ((orderCore xs).result.1 = true ↔ bitsValue (xs.map Prod.fst) < bitsValue (xs.map Prod.snd)) ∧
    ((orderCore xs).result.2 = true ↔ bitsValue (xs.map Prod.fst) = bitsValue (xs.map Prod.snd)) ∧
    (orderCore xs).steps=10*xs.length := by
  induction xs with
  | nil => simp [orderCore, bitsValue]
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    obtain ⟨hlt,heq,hs⟩ := ih
    have ht1 : (orderCore xs).result.1 = true ↔
        bitsValue (xs.map Prod.fst) < bitsValue (xs.map Prod.snd) := hlt
    have ht2 : (orderCore xs).result.2 = true ↔
        bitsValue (xs.map Prod.fst) = bitsValue (xs.map Prod.snd) := heq
    simp only [orderCore, List.length_cons, Bool.or_eq_true, Bool.and_eq_true,
      List.map_cons, bitsValue, ht1, ht2, hs]
    cases a <;> cases b <;> simp <;> omega

theorem zip_map_fst {α β : Type*} (a : List α) (b : List β) (h : a.length=b.length) :
    (a.zip b).map Prod.fst = a := by
  induction a generalizing b with
  | nil => simp
  | cons a as ih =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp [ih bs h]

theorem zip_map_snd {α β : Type*} (a : List α) (b : List β) (h : a.length=b.length) :
    (a.zip b).map Prod.snd = b := by
  induction a generalizing b with
  | nil =>
    have he : b=[] := List.length_eq_zero_iff.mp h.symm
    simp [he]
  | cons a as ih =>
    cases b with
    | nil => simp at h
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp [ih bs h]

def compareBits (a b : List Bool) : Meter Bool :=
  let c := orderCore (a.zip b)
  ⟨c.result.1,c.steps⟩

theorem compareBits_exact (a b : List Bool) (h : a.length=b.length) :
    ((compareBits a b).result=true ↔ bitsValue a < bitsValue b) ∧
    (compareBits a b).steps=10*a.length := by
  have ho := orderCore_exact (a.zip b)
  simp only [zip_map_fst a b h, zip_map_snd a b h, List.length_zip, ← h, min_self] at ho
  exact ⟨ho.1,ho.2.2⟩

def addBits (a b : List Bool) : Meter (List Bool) :=
  let c := addCore false (a.zip b)
  ⟨c.result.1,c.steps⟩

theorem addBits_exact (a b : List Bool) (h : a.length=b.length) :
    (addBits a b).result.length=a.length ∧
      bitsValue (addBits a b).result=(bitsValue a+bitsValue b)%2^a.length ∧
      (addBits a b).steps=12*a.length := by
  have hv := addCore_exact false (a.zip b)
  have hs := addCore_shape false (a.zip b)
  simp only [zip_map_fst a b h, zip_map_snd a b h, List.length_zip, ← h,
    min_self, Bool.toNat_false, add_zero] at hv hs
  change (addCore false (a.zip b)).result.1.length = a.length ∧
    bitsValue (addCore false (a.zip b)).result.1 =
      (bitsValue a+bitsValue b)%2^a.length ∧ (addCore false (a.zip b)).steps=12*a.length
  refine ⟨hs.1,?_,hs.2⟩
  rw [← hv, Nat.add_mul_mod_self_left]
  apply (Nat.mod_eq_of_lt _).symm
  rw [← hs.1]
  exact bitsValue_lt _

#print axioms full_adder
#print axioms addCore_exact
#print axioms orderCore_exact
#print axioms compareBits_exact
#print axioms addBits_exact

end AOracleMachineTime

