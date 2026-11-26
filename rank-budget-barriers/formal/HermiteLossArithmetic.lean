import J9PrintedSchedule
import Mathlib.Tactic

/-! Exact finite arithmetic beneath the tapered Hermite loss. No
infinite geometric series or uniform multiplicities are assumed. -/
namespace HermiteLoss
open scoped BigOperators

def taper (u h i : ℕ) : ℕ := h * (u-i)

def sourceH (M u : ℕ) : ℕ := (3*M+u-1)/u

def squareMass (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, 2^(n-1-k)*(k+1)^2

theorem squareMass_succ (n : ℕ) :
    squareMass (n+1)=2*squareMass n+(n+1)^2 := by
  unfold squareMass
  rw [Finset.sum_range_succ, show n+1-1-n=0 by omega, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Finset.mem_range.mp hk
  have he : n+1-1-k=(n-1-k)+1 := by omega
  rw [he,pow_succ]
  ring

theorem squareMass_closed (n : ℕ) :
    squareMass n+(n^2+4*n+6)=6*2^n := by
  induction n with
  | zero => norm_num [squareMass]
  | succ n ih =>
    change squareMass (n+1)+((n+1)^2+4*(n+1)+6)=6*2^(n+1)
    rw [squareMass_succ,pow_succ]
    calc
      _ = 2*(squareMass n+(n^2+4*n+6)) := by ring
      _ = _ := by rw [ih]; ring

theorem squareMass_cap (n : ℕ) : squareMass n ≤ 6*2^n := by
  have h := squareMass_closed n
  omega

theorem taper_decreases (u h i j : ℕ) (hi : i≤j) : taper u h j ≤ taper u h i :=
  Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hi _)

theorem taper_lipschitz (u h i j : ℕ) (hi : i≤j) :
    taper u h i - taper u h j ≤ h*(j-i) := by
  rw [taper,taper,← Nat.mul_sub_left_distrib]
  exact Nat.mul_le_mul_left _ (by omega)

theorem h_cover (M u : ℕ) (hu : 0<u) : 3*M ≤ sourceH M u * u :=
  J9PrintedSchedule.le_roundup_mul (3*M) u hu

theorem h_upper (M u : ℕ) (hM : u≤M) : sourceH M u*u ≤4*M := by
  unfold sourceH
  exact (Nat.div_mul_le_self _ _).trans (by omega)

theorem q_cap (M u i : ℕ) (hM : u≤M) :
    taper u (sourceH M u) i ≤ 4*M := by
  exact (Nat.mul_le_mul_left _ (Nat.sub_le u i)).trans (h_upper M u hM)

theorem nonzero_node_active (u h i : ℕ) (hh : 0<h) :
    0<taper u h i ↔ i<u := by
  unfold taper
  rw [Nat.mul_pos_iff_of_pos_left hh, Nat.sub_pos_iff_lt]

/-- The arithmetic margin between the two exact losses and the source
receiving precision. The optional signed coefficients use the sharper
evaluation exponent j(a+1-i), rather than j(a+1). -/
theorem source_loss_fits (p M a i u j D : ℕ)
    (hM : u≤M) (hj : j < taper u (sourceH M u) i) :
    p+6*sourceH M u*D+j*(a+1-i) ≤
      J9PrintedSchedule.precision p (sourceH M u) D M a := by
  have hj4 := hj.le.trans (q_cap M u i hM)
  have hJ : j*(a+1-i) ≤ 4*M*(a+1) :=
    Nat.mul_le_mul hj4 (Nat.sub_le _ _)
  have hD : 6*sourceH M u*D ≤ 8*sourceH M u*D :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show 6≤(8:ℕ) by decide))
  have h4 : 4*M*(a+1) ≤ 8*M*(a+1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show 4≤(8:ℕ) by decide))
  unfold J9PrintedSchedule.precision
  omega

#print axioms squareMass_closed
#print axioms squareMass_cap
#print axioms taper_lipschitz
#print axioms h_cover
#print axioms q_cap
#print axioms source_loss_fits

end HermiteLoss

