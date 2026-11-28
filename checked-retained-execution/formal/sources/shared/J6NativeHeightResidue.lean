import J6NativeHeightClearing
import DenominatorBudget
import Mathlib.Tactic

/-! The exact clearing equality persists in the native receiving ring.
In particular the raw common denominator need not be a unit modulo a
power of two. It is multiplied before the centered lift, not inverted. -/
namespace J6NativeHeightResidue
open J6NativeHeight
open scoped BigOperators
variable {R P : Type*} [CommRing R] [Fintype P] [DecidableEq P]

def ringEntry (c : R) (y x : Bool) : R :=
  if y then (if x then c else 0) else 1 - (if x then c else 0)

theorem entry_residue (n d : ℤ) (c : R) (hc : (d:R)*c = (n:R)) (y x : Bool) :
    (entry n d y x : R) = (d : R) * ringEntry c y x := by
  cases y <;> cases x <;> simp [entry,ringEntry,mul_sub,hc]

def residueSlot (A B : (P → Bool) → Bool) (read : P → (P → Bool) → Bool) (c : R) : R :=
  ∑ y : P → Bool, ∑ x : P → Bool,
    if A y && B x then ∏ p, ringEntry c (y p) (read p x) else 0

theorem residueClearing (A B : (P → Bool) → Bool) (read : P → (P → Bool) → Bool)
    (n d : ℤ) (c : R) (hc : (d:R)*c = (n:R)) :
    (numerator A B read n d : R) = (d:R)^Fintype.card P * residueSlot A B read c := by
  have hlocal (y x : P → Bool) : (↑(∏ p, entry n d (y p) (read p x)) : R) =
      (d:R)^Fintype.card P * ∏ p, ringEntry c (y p) (read p x) := by
    push_cast
    simp only [entry_residue _ _ _ hc,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  unfold numerator residueSlot
  simp only [Int.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (A y && B x) = true
  · simpa [h] using hlocal y x
  · simp [h]

/-- Being the correct two-local scalar automatically supplies the needed
cross-multiplied identity even when the raw denominator is not a unit. -/
theorem scalarClearing (map : DenominatorBudget.TwoLocal →+* R)
    (c : DenominatorBudget.TwoLocal) (n d : ℤ) (hd : d ≠ 0)
    (hc : DenominatorBudget.twoLocalRat c = (n:ℚ)/(d:ℚ)) :
    (d:R)*map c = (n:R) := by
  have he : (d:DenominatorBudget.TwoLocal)*c = n := by
    apply DenominatorBudget.twoLocalRat_injective
    have hd' : (d:ℚ) ≠ 0 := by exact_mod_cast hd
    rw [map_mul,map_intCast,map_intCast,hc]
    field_simp
  simpa only [map_mul,map_intCast] using congrArg map he

#print axioms entry_residue
#print axioms residueClearing
#print axioms scalarClearing
end J6NativeHeightResidue
