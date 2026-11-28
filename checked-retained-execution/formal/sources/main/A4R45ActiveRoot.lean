import A4R45PrintedLoad
import J6ActiveSchedule

/-! Active original signed coordinate and true printed receiving bit width
on the saturated A4 root. No timing claim for obtaining the named value. -/
namespace A4R45ActiveRoot
open scoped Classical Polynomial
open J6ActiveSchedule J9PrintedSchedule P1DyadicGrid A4R45PrintedLoad
set_option autoImplicit false
set_option warningAsError true

theorem printed_minus_one_is_active (ell M : ℕ) (big : 131072≤ell) (hM : 0<M) :
    (-1:ℤ)∈active (rootA ell) M (rootU ell) := by
  have hu : 0<rootU ell := by
    unfold rootU
    exact Nat.div_pos big (by decide)
  have hgrid : (-1:ℤ)∈grid (rootA ell) := by
    rw [mem_grid]
    have h := pow₂_pos (rootA ell)
    omega
  rw [active,Finset.mem_filter]
  refine ⟨Finset.mem_erase.mpr ⟨by decide,hgrid⟩,?_⟩
  unfold order height
  have hv : padicValInt 2 (-1)=0 := by simp
  rw [hv,Nat.sub_zero]
  exact Nat.mul_pos (Nat.div_pos (by omega) hu) hu

theorem printed_box_width (ell p₀ : ℕ) (big : 131072≤ell)
    (hp : p₀≤wireCount ell+1) :
    2*wireCount ell <
      childPrecision p₀ (rootA ell) (wireCount ell) (rootU ell) (-1) ∧
    childPrecision p₀ (rootA ell) (wireCount ell) (rootU ell) (-1) ≤
      (wireCount ell+1)+40*(wireCount ell)^2 := by
  let m := wireCount ell
  let u := rootU ell
  let a := rootA ell
  let L := 2^a
  have hm : 0<m := by dsimp [m,wireCount]; positivity
  have uPos : 0<u := Nat.div_pos big (by decide)
  have ua : u≤a+1 := by change u≤2*u+1; omega
  have aL : a+1≤L := next_le_two_power a
  have ae : a≤ell := by
    change 2*(ell/131072)≤ell
    calc
      _ ≤ 131072*(ell/131072) := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have Lm : L≤m := Nat.pow_le_pow_right (by decide) ae
  have um : u≤m := (ua.trans aL).trans Lm
  have hm4 : height m u≤4*m :=
    (Nat.le_mul_of_pos_right _ uPos).trans (height_bounds m u uPos um).2
  have sz : p₀≤m+1 := hp
  change 2*m < childPrecision p₀ a m u (-1) ∧
    childPrecision p₀ a m u (-1)≤(m+1)+40*m^2
  unfold childPrecision J9PrintedSchedule.precision
  have hv : padicValInt 2 (-1)=0 := by simp
  rw [hv,pow_zero,Nat.div_one]
  change 2*m < p₀+8*height m u*L+8*m*(a+1) ∧
    p₀+8*height m u*L+8*m*(a+1)≤(m+1)+40*m^2
  constructor
  · have low : 8*m≤8*m*(a+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  · have t₁ : 8*height m u*L≤8*(4*m)*m :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hm4) Lm
    have t₂ : 8*m*(a+1)≤8*m*m :=
      Nat.mul_le_mul (le_refl _) (aL.trans Lm)
    exact (Nat.add_le_add (Nat.add_le_add sz t₁) t₂).trans_eq (by ring)

#print axioms printed_minus_one_is_active
#print axioms printed_box_width
end A4R45ActiveRoot
