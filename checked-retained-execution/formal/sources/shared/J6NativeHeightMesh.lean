import J6NativeHeightClearing
import J6SourcePrecision
import Mathlib.Tactic

/-! Literal integer denominator and numerator at the chosen odd
mesh. They need not be reduced: cancellation is not used for the
height or the rational clearing equality. -/
namespace J6NativeHeightMesh
open scoped BigOperators
open J6Mesh J6NativeHeight J6NativeHeightClearing

def posProd (L t : ℕ) : ℕ := ∏ j ∈ Finset.range t, (L+(j+1))
def negProd (L t : ℕ) : ℕ := ∏ j ∈ Finset.range t, (L-(j+1))

theorem products_bound (L t : ℕ) (ht : t < L) :
    posProd L t ≤ (2*L)^t ∧ negProd L t ≤ (2*L)^t ∧ 0 < negProd L t := by
  refine ⟨?_,?_,?_⟩
  · unfold posProd
    calc
      _ ≤ ∏ _j ∈ Finset.range t, (2*L) := Finset.prod_le_prod' fun j hj => by
        have hj₀ := Finset.mem_range.mp hj
        omega
      _ = _ := by simp
  · unfold negProd
    calc
      _ ≤ ∏ _j ∈ Finset.range t, (2*L) := Finset.prod_le_prod' fun j _ => by omega
      _ = _ := by simp
  · unfold negProd
    exact Finset.prod_pos fun j hj => by
      have hj₀ := Finset.mem_range.mp hj
      omega

theorem grid_ratio_fraction (L t : ℕ) (ht : t < L) :
    LayerRecovery.gridRatio L t = (posProd L t : ℚ)/(negProd L t : ℚ) := by
  unfold LayerRecovery.gridRatio
  rw [Finset.prod_div_distrib]
  unfold posProd negProd
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hj₀ := Finset.mem_range.mp hj
  rw [Nat.cast_sub (by omega : j+1 ≤ L),Nat.cast_add,Nat.cast_one]

def sampleNum (m : ℕ) (i : Fin (m+1)) : ℤ := -(posProd (L m) (index m i) : ℤ)
def sampleDen (m : ℕ) (i : Fin (m+1)) : ℤ := negProd (L m) (index m i)

theorem mesh_fraction (m : ℕ) (i : Fin (m+1)) :
    point m i = (sampleNum m i : ℚ)/(sampleDen m i : ℚ) := by
  unfold point sampleNum sampleDen
  rw [grid_ratio_fraction _ _ (address_index m i).2.2.2]
  push_cast
  rw [neg_div]

theorem mesh_bounds (m : ℕ) (i : Fin (m+1)) :
    0 < sampleDen m i ∧
    |sampleNum m i| ≤ (2:ℤ)^(index m i*(a m+1)) ∧
    |sampleDen m i| ≤ (2:ℤ)^(index m i*(a m+1)) := by
  obtain ⟨hp,hd,hd0⟩ := products_bound (L m) (index m i) (address_index m i).2.2.2
  have hbase : 2*L m = 2^(a m+1) := by rw [J6Mesh.L,pow_succ,Nat.mul_comm]
  have hexp : (2*L m)^index m i = 2^(index m i*(a m+1)) := by
    rw [hbase,← pow_mul,Nat.mul_comm (a m+1)]
  rw [hexp] at hp hd
  unfold sampleDen sampleNum
  rw [abs_neg,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
  exact ⟨by exact_mod_cast hd0,by exact_mod_cast hp,by exact_mod_cast hd⟩

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- An explicit integer, proved to equal the cleared physical expression
and to fit the exact printed precision of this same address. -/
theorem mesh_centered_numerator (m base : ℕ) (i : Fin (m+1))
    (hP : Fintype.card P = M m)
    (A B : (P → Bool) → Bool) (read : P → (P → Bool) → Bool) :
    ∃ z : ℤ, (z : ℚ) = (sampleDen m i : ℚ)^M m * rationalSlot A B read (point m i) ∧
      2*|z| < (↑((2:ℕ)^J6SourcePrecision.printed m base):ℤ) := by
  obtain ⟨hd,hn,hdd⟩ := mesh_bounds m i
  let z := numerator A B read (sampleNum m i) (sampleDen m i)
  refine ⟨z,?_,?_⟩
  · have hs := explicit_cleared_numerator A B read (sampleNum m i) (sampleDen m i) hd.ne'
    rwa [hP,← mesh_fraction] at hs
  · exact J6SourcePrecision.centered_fit_printed m base i z
      (physical_height m (index m i) hP A B read _ _ hn hdd)

#print axioms products_bound
#print axioms grid_ratio_fraction
#print axioms mesh_fraction
#print axioms mesh_bounds
#print axioms mesh_centered_numerator
end J6NativeHeightMesh
