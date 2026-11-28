import V8CapacitySpecialLargeMatrix
import V8CapacitySpecialProfile
import V8CapacitySpecialSmithSplit
import V8CapacityNativeLift

/-! The large-residue numerical answer for the exact original A2
matrix. Equality of all cumulative counts identifies the multiset of
Smith exponents, not just the generic rank or a selected lower bound. -/
namespace V8CapacitySpecialLargeCapacity
open scoped Classical BigOperators
open V8CapacitySymbolic V8CapacityNativeMatrix V8CapacityMonicBasis
open V8CapacityIntegrated V8CapacitySmith V8CapacityWidthGrid
open V8CapacityWidthUpper V8CapacityActiveWitness V8CapacityNativeA3 V8CapacityWidthRank
open V8CapacitySpecialPrimitive V8CapacitySpecialSplit V8CapacitySpecialProfile
open V8CapacitySpecialLargeMatrix

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1050000

variable {O H : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [IsPrincipalIdealRing O] [Fintype H]
variable {π : O} {q : ℕ} (D : V8CapacityDigits.Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (k P : ℕ)

local notation "E" => Digits H k
local notation "I" => Grid H P k
local notation "J" => Columns H π P k
local notation "rdeg" => (@rowDegree E _ (DegreeCap P k))
local notation "CM" => monicC π P k D hq
local notation "W" => weighted π q rdeg (CM : Matrix I J O)
local notation "SM" => matrixPowered π hMax W
local notation "S" => (SM).2

include hq₂ h0 hπ in
def diagonalSplit (hk : 0<k) (large : DegreeCap P k<q) :
    Split π (matrixImage W) J := by
  refine matrixSplit π W (primitiveMatrix D hq hπ hMax P k)
    (pivotMatrix D hq hMax P k) (colμ π P k) ?_ ?_
  · have h := primitive_left_inverse (H:=H) D hq hπ hMax P k hk
    refine h.trans ?_
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.one_apply]
    · simp only [Matrix.one_apply,if_neg hij]
  · have h := exact_diagonal_factor (H:=H) D hq hq₂ h0 hπ hMax P k large
    refine h.trans ?_
    apply congrArg (fun T : Matrix J J O => primitiveMatrix D hq hπ hMax P k*T)
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
    · simp [hij]


include hq₂ h0 hπ in
/-- Quantifies over every threshold, hence identifies each exponent
with its multiplicity in the chosen actual Smith presentation. -/
theorem exact_large_profile (hk : 0<k) (large : DegreeCap P k<q) (b : ℕ) :
    Fintype.card {i : Fin (SM).1 // (S).exponent i≤b} =
      Fintype.card {j : J // colμ π P k j≤b} :=
  same_exponent_profile (fromSmith S) (diagonalSplit D hq hq₂ h0 hπ hMax k P hk large)
    hπ hMax b

include hq₂ h0 hπ in
theorem large_active_count (hk : 0<k) (hP : 0<P) (large : DegreeCap P k<q) :
    Fintype.card (Active S P)=Fintype.card J := by
  let e : Active S P ≃ {i : Fin (SM).1 // (S).exponent i≤P-1} :=
    { toFun := fun i => ⟨i.val,by have h := i.property; change (S).exponent i.val<P at h; omega⟩
      invFun := fun i => ⟨i.val,by have h := i.property; omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f : {j : J // colμ π P k j≤P-1} ≃ J :=
    { toFun := Subtype.val
      invFun := fun j => ⟨j,by have h := chosen_low π P k j; omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans
    ((exact_large_profile D hq hq₂ h0 hπ hMax k P hk large (P-1)).trans (Fintype.card_congr f))

variable [Fintype (IsLocalRing.ResidueField O)]

local notation "κ" => IsLocalRing.ResidueField O

include hq₂ h0 hπ in
theorem capacity_formula (hk : 0<k) (hP : 0<P) (large : DegreeCap P k<q)
    (e : Fin q ≃ κ) :
    Fintype.card ((H → κ) × Active S P)=
      q^(Fintype.card H)*Fintype.card J := by
  have he := Fintype.card_congr e
  simp only [Fintype.card_fin] at he
  rw [Fintype.card_prod,Fintype.card_fun,← he,
    large_active_count D hq hq₂ h0 hπ hMax k P hk hP large]

#print axioms diagonalSplit
#print axioms exact_large_profile
#print axioms large_active_count
#print axioms capacity_formula
end
end V8CapacitySpecialLargeCapacity

