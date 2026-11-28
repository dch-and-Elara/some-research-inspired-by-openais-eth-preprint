import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-! # Exact finite constants for the printed J7 root placement -/

namespace J7PrintedParams
noncomputable section

/-- Conservative collision/deviation radius and matching-deviation
radius. Their squares cover 32M and 25M, respectively. -/
def mu (N D : ℕ) : ℚ := 24*(N:ℚ)/D
def rho (N D : ℕ) : ℚ := mu N D / 16
def delta (N D : ℕ) : ℚ := mu N D / 128
def pinMeanUpper (N D : ℕ) : ℚ := (64/63:ℚ)*((N:ℚ)/D)
def bUpper (N D L : ℕ) : ℕ := (⌈2*mu N D/L⌉ : ℤ).toNat

theorem upper_rounding (x : ℚ) (hx : 0 ≤ x) :
    x ≤ ((⌈x⌉ : ℤ).toNat : ℚ) ∧ ((⌈x⌉ : ℤ).toNat : ℚ) ≤ x+1 := by
  have hi : 0 ≤ (⌈x⌉ : ℤ) := Int.ceil_nonneg hx
  have hcast : ((⌈x⌉ : ℤ).toNat : ℚ) = (⌈x⌉ : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hi
  rw [hcast]
  exact ⟨Int.le_ceil _, (Int.ceil_lt_add_one _).le⟩

structure Margin (N D L Δ : ℕ) : Prop where
  rho_nonneg : 0 ≤ rho N D
  delta_nonneg : 0 ≤ delta N D
  word : 32*(24*(N:ℚ)) ≤ (rho N D)^2
  mark : (24*(N:ℚ))*5^2 ≤ (delta N D)^2
  capacity : mu N D + rho N D ≤ (bUpper N D L : ℚ)*L
  endpointMargin : 2*(bUpper N D L : ℚ)+delta N D ≤
      (mu N D - pinMeanUpper N D - 2*rho N D)*(1/2:ℚ)^5
  padded : (bUpper N D L : ℚ)*L ≤ 3*mu N D
  collision : 32*(24*(N:ℚ)) ≤ 2*(24*(N:ℚ))*Δ

/-- Original packing inequalities and an explicit large-root threshold
suffice. No asymptotic inequalities or implicit large constants remain
in the invocation of this theorem. -/
theorem margin (N D L Δ : ℕ)
    (hD : 0 < D) (hL : 131072 ≤ L)
    (packing1 : 2*D^2*Δ ≤ 24*N) (packing2 : L*D ≤ 24*N)
    (packing3 : 2*L ≤ Δ) : Margin N D L Δ := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hLq : (131072 : ℚ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℚ) < L := by linarith
  have hMq : (0 : ℚ) ≤ 24*(N:ℚ) := by positivity
  have hnum : (2:ℚ)*(D:ℚ)^2*Δ ≤ 24*(N:ℚ) := by exact_mod_cast packing1
  have hp2 : (L:ℚ)*D ≤ 24*(N:ℚ) := by exact_mod_cast packing2
  have hp3 : (2:ℚ)*L ≤ Δ := by exact_mod_cast packing3
  have hμL : (L:ℚ) ≤ mu N D := (le_div_iff₀ hDq).2 hp2
  have hμ : 0 ≤ mu N D := hLpos.le.trans hμL
  have hDelta : (262144:ℚ) ≤ Δ := by linarith
  have hμsq : 2*(Δ:ℚ)*(24*(N:ℚ)) ≤ (mu N D)^2 := by
    unfold mu
    rw [div_pow]
    refine (le_div_iff₀ (by positivity : 0 < (D:ℚ)^2)).2 ?_
    have hh := mul_le_mul_of_nonneg_right hnum hMq
    convert hh using 1 <;> ring
  have h8 : (8192:ℚ)*(24*(N:ℚ)) ≤ (mu N D)^2 :=
    (mul_le_mul_of_nonneg_right (by linarith : (8192:ℚ) ≤ 2*Δ) hMq).trans hμsq
  have h409 : (409600:ℚ)*(24*(N:ℚ)) ≤ (mu N D)^2 :=
    (mul_le_mul_of_nonneg_right (by linarith : (409600:ℚ) ≤ 2*Δ) hMq).trans hμsq
  have hρ : 0 ≤ rho N D := div_nonneg hμ (by norm_num)
  have hδ : 0 ≤ delta N D := div_nonneg hμ (by norm_num)
  have hword : 32*(24*(N:ℚ)) ≤ (rho N D)^2 := by
    unfold rho
    nlinarith only [h8]
  have hmark : (24*(N:ℚ))*5^2 ≤ (delta N D)^2 := by
    unfold delta
    nlinarith only [h409]
  have hround := upper_rounding (2*mu N D/L) (by positivity)
  change 2*mu N D/L ≤ (bUpper N D L : ℚ) ∧
    (bUpper N D L : ℚ) ≤ 2*mu N D/L + 1 at hround
  have hB1 := (div_le_iff₀ hLpos).1 hround.1
  have hCap : mu N D + rho N D ≤ (bUpper N D L : ℚ)*L := by
    unfold rho
    linarith
  have hB2 := mul_le_mul_of_nonneg_right hround.2 hLpos.le
  have hB3 : (2*mu N D / (L:ℚ) + 1)*L = 2*mu N D+L := by
    rw [add_mul,div_mul_cancel₀ _ hLpos.ne',one_mul]
  rw [hB3] at hB2
  have hPad : (bUpper N D L : ℚ)*L ≤ 3*mu N D := by linarith
  have hSmall : 2*mu N D/L ≤ mu N D / 512 := by
    refine (div_le_iff₀ hLpos).2 ?_
    have hh := mul_le_mul_of_nonneg_left (by linarith : (1024:ℚ) ≤ L)
      (show 0 ≤ mu N D/512 by positivity)
    linarith
  have hBsmall : 2*(bUpper N D L : ℚ) ≤ mu N D / 128 := by
    have hm : (1024:ℚ) ≤ mu N D := by linarith
    linarith [hround.2]
  have hPin : pinMeanUpper N D ≤ mu N D/16 := by
    unfold pinMeanUpper mu
    have hh : 0 ≤ (N:ℚ)/D := by positivity
    have he : 24*(N:ℚ)/D = 24*((N:ℚ)/D) := by rw [mul_div_assoc]
    rw [he]
    linarith
  have hEnd : 2*(bUpper N D L : ℚ)+delta N D ≤
      (mu N D - pinMeanUpper N D - 2*rho N D)*(1/2:ℚ)^5 := by
    unfold delta rho
    norm_num
    linarith
  have hColl : 32*(24*(N:ℚ)) ≤ 2*(24*(N:ℚ))*Δ := by
    rw [mul_right_comm 2]
    exact mul_le_mul_of_nonneg_right (by linarith) hMq
  exact ⟨hρ,hδ,hword,hmark,hCap,hEnd,hPad,hColl⟩

#print axioms upper_rounding
#print axioms margin

end
end J7PrintedParams
