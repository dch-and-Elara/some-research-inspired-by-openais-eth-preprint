import P1DyadicGrid
import J9PrintedSchedule
import Mathlib.Tactic

/-! Literal signed grid, degree budget, and child scheduling inequalities
of Appendix D, lines 85, 250–273, 338–346 and 525–528. -/
namespace J6ActiveSchedule
open scoped BigOperators
open P1DyadicGrid

def height (M u : ℕ) : ℕ := (3*M+u-1)/u

def order (M u : ℕ) (t : ℤ) : ℕ := height M u * (u-padicValInt 2 t)

def active (a M u : ℕ) : Finset ℤ :=
  ((grid a).erase 0).filter (fun t => 0 < order M u t)

def childPrecision (p a M u : ℕ) (t : ℤ) : ℕ :=
  J9PrintedSchedule.precision p (height M u) (2^a / 2^(padicValInt 2 t)) M a

theorem height_bounds (M u : ℕ) (hu : 0 < u) (huM : u ≤ M) :
    3*M ≤ height M u * u ∧ height M u * u ≤ 4*M := by
  constructor
  · exact J9PrintedSchedule.le_roundup_mul (3*M) u hu
  · unfold height
    exact (Nat.div_mul_le_self _ _).trans (by omega)

theorem order_bound (M u : ℕ) (t : ℤ) (hu : 0 < u) (huM : u ≤ M) :
    order M u t ≤ 4*M := by
  unfold order
  exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (height_bounds M u hu huM).2

theorem child_monotone (p a M u : ℕ) (t : ℤ) (hM : 0 < M) :
    p < childPrecision p a M u t := by
  have h : 0 < 8*M*(a+1) := by positivity
  unfold childPrecision J9PrintedSchedule.precision
  omega

theorem child_shrinks (M m : ℕ) (hM : 0 < M) (hpack : 32*m ≤ 3*M) :
    8*m ≤ M ∧ m < M := by omega

def oddGrid (a : ℕ) : Finset ℤ := (grid a).filter Odd

theorem oddGrid_card (a : ℕ) : (oddGrid a).card = 2^a := by
  let L := pow₂ a
  let f : ℤ → ℤ := fun z => 2*z+1
  have hf : Function.Injective f := by intro x y h; dsimp [f] at h; omega
  have he : oddGrid a = (Finset.Ico ((-L)/2) (L/2)).image f := by
    ext q
    simp only [oddGrid,Finset.mem_filter,mem_grid,Finset.mem_image,Finset.mem_Ico]
    constructor
    · rintro ⟨hq,⟨j,hj⟩⟩
      change -L ≤ q ∧ q < L at hq
      exact ⟨j, ⟨by omega,by omega⟩,by dsimp [f]; omega⟩
    · rintro ⟨j,hj,rfl⟩
      change ((-L ≤ f j ∧ f j < L) ∧ _)
      dsimp [f]
      exact ⟨⟨by omega,by omega⟩,⟨j,by omega⟩⟩
  rw [he,Finset.card_image_of_injective _ hf,Int.card_Ico]
  have hh : L/2 - (-L)/2 = L := by omega
  rw [hh]
  have hL : L = Int.ofNat ((2:ℕ)^a) := by simp [L,pow₂,Int.ofNat_eq_coe]
  rw [hL]
  rfl

theorem oddGrid_subset_active (a M u : ℕ) (hu : 0 < u) (huM : u ≤ M) :
    oddGrid a ⊆ active a M u := by
  intro t ht
  have ⟨ht, ho⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_erase.mpr ⟨odd_int_ne_zero ho,ht⟩,?_⟩
  unfold order
  rw [odd_valuation_zero ho, Nat.sub_zero]
  exact (show 0 < 3*M by omega).trans_le (height_bounds M u hu huM).1

theorem total_order_large (a M u : ℕ) (hu : 0 < u) (huM : u ≤ M) :
    J9PrintedSchedule.degreeBound M (2^a) < ∑ t ∈ active a M u, order M u t := by
  have hsum : (∑ t ∈ oddGrid a, order M u t) = (2^a) * (height M u * u) := by
    calc
      _ = ∑ _t ∈ oddGrid a, height M u * u := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [order,odd_valuation_zero (Finset.mem_filter.mp ht).2,Nat.sub_zero]
      _ = _ := by rw [Finset.sum_const,oddGrid_card]; simp
  have hLp : 0 < (2:ℕ)^a := by positivity
  have hMp : 0 < M := hu.trans_le huM
  calc
    J9PrintedSchedule.degreeBound M (2^a) ≤ 2*(M*(2^a)) := by
      unfold J9PrintedSchedule.degreeBound
      calc
        _ ≤ M*(2*(2^a)) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = _ := by ring
    _ < 3*(M*(2^a)) := Nat.mul_lt_mul_of_pos_right (by decide) (mul_pos hMp hLp)
    _ ≤ (2^a)*(height M u*u) := by
      simpa [mul_left_comm, mul_comm, mul_assoc] using
        Nat.mul_le_mul_left ((2:ℕ)^a) (height_bounds M u hu huM).1
    _ = _ := hsum.symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (oddGrid_subset_active a M u hu huM)

theorem active_order_pos (a M u : ℕ) (t : ℤ) (ht : t ∈ active a M u) :
    0 < order M u t := (Finset.mem_filter.mp ht).2

#print axioms height_bounds
#print axioms order_bound
#print axioms child_monotone
#print axioms child_shrinks
#print axioms oddGrid_card
#print axioms total_order_large
#print axioms active_order_pos
end J6ActiveSchedule