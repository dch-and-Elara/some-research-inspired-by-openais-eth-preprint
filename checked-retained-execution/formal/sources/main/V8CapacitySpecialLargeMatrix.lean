import V8CapacitySpecialPrimitive
import V8CapacityGridOrder

/-! Large residue specialization, on the actual A2 coefficient
matrix: every Newton weight is 1, and scaled native columns split
by a left inverse obtained from their distinct ordinary monomial pivots. -/
namespace V8CapacitySpecialLargeMatrix
open scoped Polynomial Classical BigOperators
open V8CapacitySymbolic V8CapacityNativeMatrix V8CapacitySpecialPrimitive
open V8CapacityMonicBasis V8CapacityGridOrder V8CapacityFactorial V8CapacityNewtonGrid
open V8CapacityIntegrated

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

theorem debt_zero_below (q n : ℕ) (hq : 0<q) (hn : n<q) : debt q n=0 := by
  unfold debt
  apply Finset.sum_eq_zero
  intro u _
  exact Nat.div_eq_of_lt (hn.trans_le (by
    simpa only [pow_one] using Nat.pow_le_pow_right hq (show 1≤u+1 by omega)))

variable {O H : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [Fintype H]
variable {π : O} {q : ℕ} (D : V8CapacityDigits.Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (P k : ℕ)

local notation "E" => Digits H k
local notation "I" => Grid H P k
local notation "J" => Columns H π P k
local notation "rdeg" => (@rowDegree E _ (DegreeCap P k))
local notation "CM" => monicC π P k D hq

include hq in
theorem grid_no_debt (large : DegreeCap P k<q) (i : I) :
    multiDebt q (rdeg i)=0 := by
  unfold multiDebt
  apply Finset.sum_eq_zero
  intro e _
  exact debt_zero_below q _ hq ((Nat.lt_succ_iff.mp (i.val e).isLt).trans_lt large)

theorem weighted_is_unscaled (large : DegreeCap P k<q) :
    weighted π q rdeg (CM : Matrix I J O)=CM := by
  ext i j
  simp only [weighted,Matrix.of_apply,grid_no_debt hq P k large,pow_zero,one_mul]

theorem normalized_monic_eval (large : DegreeCap P k<q) (i : I) (x : E → O) :
    MvPolynomial.eval x (basisPoly D hq (rdeg i)) =
      tensorNorm D hq hq₂ h0 hπ (rdeg i) x := by
  have h : tensor D hq (rdeg i) x = tensorNorm D hq hq₂ h0 hπ (rdeg i) x := by
    rw [tensor_factor D hq hq₂ h0 hπ,grid_no_debt hq P k large,pow_zero,one_mul]
  rw [← h,basis_eval,tensor]
  apply Finset.prod_congr rfl
  intro e _
  exact (Fin.prod_univ_eq_prod_range _ _).symm

/-- This finite triangular test is stated generically, so that
definitional equality of concrete total-degree row enumerations is
not used by the proof. -/
theorem coordinates_unique_from_grid
    {R A B : Type*} [CommRing R] [Fintype A] [DecidableEq A]
    (V : Matrix A A R) (hDet : IsUnit V.det)
    (basis : A → MvPolynomial B R) (x : A → B → R)
    (hEntry : ∀ i j, V i j=MvPolynomial.eval (x i) (basis j))
    (a b : A → R)
    (h : (∑ j : A, a j • basis j) = ∑ j : A, b j • basis j) : a=b := by
  have hv : V.mulVec a=V.mulVec b := by
    funext i
    have hh := congrArg (MvPolynomial.eval (x i)) h
    change (∑ j : A, V i j*a j) = ∑ j : A, V i j*b j
    simp_rw [hEntry i]
    simpa only [map_sum,MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,mul_comm]
      using hh
  have he (c : A → R) : (V⁻¹).mulVec (V.mulVec c)=c := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul V hDet,Matrix.one_mulVec]
  exact (he a).symm.trans ((congrArg (fun c => (V⁻¹).mulVec c) hv).trans (he b))


section GenericUnique

variable {R E' A : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
variable [Fintype E'] [Fintype A] [LinearOrder A]
variable {ρ : R} {q' : ℕ}
variable (D' : V8CapacityDigits.Digits ρ q') (hq' : 0<q')
variable (h₂ : 2≤q') (hz : D'.d ⟨0,hq'⟩=0) (hp : ρ≠0)
variable (hM : IsLocalRing.maximalIdeal R=Ideal.span ({ρ}:Set R))
variable (degree : A → E' → ℕ)
variable (order : ∀ i j, (∀ e, degree i e≤degree j e) → i≤j)

include order hM h₂ hz hp in
/-- State the square-grid argument on arbitrary finite index types.
No equality between different Fintype enumerations is needed. -/
theorem unique_weight_zero (debts : ∀ i, multiDebt q' (degree i)=0)
    (a b : A → R)
    (equal : (∑ i : A, a i • basisPoly D' hq' (degree i)) =
      ∑ i : A, b i • basisPoly D' hq' (degree i)) : a=b := by
  let V := normGrid D' hq' h₂ hz hp degree
  have hu : IsUnit V.det := norm_grid_unit D' hq' h₂ hz hp hM degree order
  have he i j : V i j=MvPolynomial.eval (nodeAt D' hq' degree i) (basisPoly D' hq' (degree j)) := by
    let x := nodeAt D' hq' degree i
    change tensorNorm D' hq' h₂ hz hp (degree j) x=MvPolynomial.eval x (basisPoly D' hq' (degree j))
    have hh := tensor_factor D' hq' h₂ hz hp (degree j) x
    rw [debts j,pow_zero,one_mul] at hh
    rw [← hh,basis_eval,tensor]
    apply Finset.prod_congr rfl
    intro e _
    unfold newton
    exact Fin.prod_univ_eq_prod_range (fun t => x e-V8CapacityDigits.node D' hq' t) (degree j e)
  exact coordinates_unique_from_grid V hu (fun i => basisPoly D' hq' (degree i))
    (nodeAt D' hq' degree) he a b equal

end GenericUnique

def monicCombination (a : I → O) : MvPolynomial E O :=
  ∑ i : I, a i • basisPoly D hq (rdeg i)

include hMax hπ hq₂ h0 in
theorem unique_monic_coordinates (large : DegreeCap P k<q) (a b : I → O)
    (h : monicCombination D hq P k a=monicCombination D hq P k b) : a=b := by
  letI : LinearOrder I := gridOrder
  apply unique_weight_zero D hq hq₂ h0 hπ hMax rdeg
    (fun i j => coordinate_le (x:=i) (y:=j)) (grid_no_debt hq P k large) a b
  exact h


def pCol (j : J) := (primitiveCol π P k hMax j).poly

include hπ in
theorem some_primitive_coefficients (j : J) :
    ∃ a : I → O, ∑ i : I, a i • basisPoly D hq (rdeg i)=pCol hMax P k j := by
  obtain ⟨a,ha⟩ := exact_monic_expansion («E»:=E) D hq (DegreeCap P k)
    (pCol hMax P k j) (primitive_degree π P k hπ hMax j)
  refine ⟨a,?_⟩
  rw [← ha]
  apply Finset.sum_congr (by ext i; simp only [Finset.mem_univ])
  exact fun _ _ => rfl

def primitiveMatrix : Matrix I J O :=
  Matrix.of fun i j => Classical.choose (some_primitive_coefficients D hq hπ hMax P k j) i

theorem primitive_expansion (j : J) :
    ∑ i : I, primitiveMatrix D hq hπ hMax P k i j • basisPoly D hq (rdeg i)=pCol hMax P k j :=
  Classical.choose_spec (some_primitive_coefficients D hq hπ hMax P k j)

include hq₂ h0 in
theorem exact_diagonal_factor (large : DegreeCap P k<q) :
    weighted π q rdeg (CM : Matrix I J O) =
      primitiveMatrix D hq hπ hMax P k * Matrix.diagonal (fun j => π^colμ π P k j) := by
  rw [weighted_is_unscaled D hq P k large]
  ext i j
  have hh := unique_monic_coordinates D hq hq₂ h0 hπ hMax P k large
    (fun i => (CM : Matrix I J O) i j)
    (fun i => (π^colμ π P k j)*primitiveMatrix D hq hπ hMax P k i j) ?_
  · rw [Matrix.mul_diagonal]
    exact (congrFun hh i).trans (mul_comm _ _)
  · unfold monicCombination
    have hg := column_expansion π P k D hq j
    change (∑ i : I, (CM : Matrix I J O) i j • basisPoly D hq (rdeg i))=_ at hg
    rw [hg]
    have he : symCol π P k j.val=(π^colμ π P k j) • pCol hMax P k j := by
      rw [MvPolynomial.smul_eq_C_mul]
      exact (primitiveCol π P k hMax j).factor
    rw [he,← primitive_expansion D hq hπ hMax P k j,Finset.smul_sum]
    simp only [smul_smul]

def pivotMatrix : Matrix J I O :=
  Matrix.of fun j i =>
    (↑((primitiveCol π P k hMax j).unit⁻¹):O) *
      (basisPoly D hq (rdeg i)).coeff (primitiveCol π P k hMax j).pivot

theorem primitive_left_inverse (hk : 0<k) :
    pivotMatrix D hq hMax P k * primitiveMatrix D hq hπ hMax P k = (1:Matrix J J O) := by
  ext i j
  let g := primitiveCol π P k hMax i
  let ev : MvPolynomial E O → O := MvPolynomial.coeff g.pivot
  have h := congrArg ev (primitive_expansion D hq hπ hMax P k j)
  change ev (∑ u : I, primitiveMatrix D hq hπ hMax P k u j • basisPoly D hq (rdeg u))=
    ev (pCol hMax P k j) at h
  simp only [ev,MvPolynomial.coeff_sum,MvPolynomial.smul_eq_C_mul,MvPolynomial.coeff_C_mul] at h
  rw [Matrix.mul_apply]
  simp only [pivotMatrix,Matrix.of_apply,mul_assoc,← Finset.mul_sum]
  have heq :
      (∑ u : I, (basisPoly D hq (rdeg u)).coeff g.pivot * primitiveMatrix D hq hπ hMax P k u j)=
      (pCol hMax P k j).coeff g.pivot := by
    simpa only [mul_comm] using h
  rw [heq,Matrix.one_apply]
  by_cases hh : i=j
  · subst j
    rw [if_pos rfl]
    change (↑(g.unit⁻¹):O)*g.poly.coeff g.pivot=1
    rw [g.hit,Units.inv_mul]
  · rw [if_neg hh]
    change (↑(g.unit⁻¹):O)*((primitiveCol π P k hMax j).poly.coeff g.pivot)=0
    rw [primitive_orthogonal π P k hk hMax i j hπ hh,mul_zero]

#print axioms debt_zero_below
#print axioms grid_no_debt
#print axioms weighted_is_unscaled
#print axioms unique_monic_coordinates
#print axioms exact_diagonal_factor
#print axioms primitive_left_inverse
end
end V8CapacitySpecialLargeMatrix

