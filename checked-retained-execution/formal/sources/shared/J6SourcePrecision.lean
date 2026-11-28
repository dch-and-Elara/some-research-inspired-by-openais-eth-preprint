import J6Precision
import Mathlib.Tactic

/-! Native odd-root precision of the fixed J6 construction. The source
ceiling h = ceil(3M/u), with odd t giving D_t = L, is used exactly. -/
namespace J6SourcePrecision
open J6Mesh J6Precision
def h (m : ℕ) := (3*M m+u m-1)/u m
def printed (m base : ℕ) := base+8*h m*L m+8*M m*(a m+1)

theorem ceiling_cover (m : ℕ) : 3*M m ≤ u m*h m := by
  have hu : 0 < u m := by
    have hb := b_pos m
    unfold u
    omega
  have hr := Nat.mod_lt (3*M m+u m-1) hu
  have hd := Nat.mod_add_div (3*M m+u m-1) (u m)
  unfold h
  omega

theorem precision_from_printed (m base : ℕ) :
    24*M m*L m ≤ u m*printed m base := by
  calc
    _ = (8*L m)*(3*M m) := by ring
    _ ≤ (8*L m)*(u m*h m) := Nat.mul_le_mul_left _ (ceiling_cover m)
    _ = u m*(8*h m*L m) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by unfold printed; omega)

theorem centered_fit_printed (m base : ℕ) (i : Fin (m+1)) (num : ℤ)
    (hAbs : |num| ≤ (↑((2:ℕ)^height m (index m i)):ℤ)) :
    2*|num| < (↑((2:ℕ)^printed m base):ℤ) :=
  centered_fit m (index m i) (printed m base) (address_index m i).2.2.1
    (precision_from_printed m base) num hAbs

#print axioms ceiling_cover
#print axioms precision_from_printed
#print axioms centered_fit_printed
end J6SourcePrecision
