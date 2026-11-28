import V8CapacityUnifiedScalarWeights
import V8CapacityUnifiedScalarIndex
import V8CapacitySpecialProfile
import V8CapacitySpecialSmithSplit

/-! Native active Newton grid for arbitrary public scalar classes.
The grid uses the same active tuples as S2, and its actual raw
evaluation image has exactly their full Smith exponent multiset. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators
open V8CapacityDigits V8CapacityNewtonGrid V8CapacitySmith
open V8CapacityWidthUpper V8CapacitySpecialSplit V8CapacitySpecialProfile

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1450000

variable {O H : Type*} [CommRing O] [IsDomain O] [Fintype H]
variable {π : O} {q : ℕ} (D : Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (s : PublicClass (O:=O) (H:=H)) (P : ℕ)

local notation "I" => S2Index q P s.depth
local notation "deg" => (indexDegree (q:=q) (P:=P) (v:=s.depth))
local notation "ord" => (fun i : I => weight q s.depth (deg i))

def gridMessages (r : I) : H → O :=
  message π s (nodeAt D hq deg r)

theorem gridMessages_permitted (r : I) : permitted π s (gridMessages D hq s P r) :=
  (message_eq_permitted π s _).mpr ⟨_,rfl⟩

def rawGrid : Matrix I I O :=
  Matrix.of fun r j => MvPolynomial.eval (gridMessages D hq s P r) (phi D hq s (deg j))

def normalGrid : Matrix I I O :=
  normGrid D hq hq₂ h0 hπ deg

theorem grid_factor :
    letI := Classical.decEq I
    rawGrid D hq s P = normalGrid D hq hq₂ h0 hπ s P * Matrix.diagonal (fun j => π^ord j) := by
  letI : DecidableEq I := Classical.decEq _
  ext r j
  rw [Matrix.mul_diagonal]
  change MvPolynomial.eval (message π s (nodeAt D hq deg r)) (phi D hq s (deg j)) =
    tensorNorm D hq hq₂ h0 hπ (deg j) (nodeAt D hq deg r)*π^ord j
  rw [phi_eval_normalized D hq hq₂ h0 hπ,mul_comm]

variable [IsLocalRing O]
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))

include hMax in
theorem abstract_grid_left {J : Type*} [Fintype J] [LinearOrder J]
    (d : J → H → ℕ) (hd : ∀ i j, (∀ e, d i e ≤ d j e) → i ≤ j) :
    letI := Classical.decEq J
    ∃ A : Matrix J J O, A * normGrid D hq hq₂ h0 hπ d = 1 := by
  let G := normGrid D hq hq₂ h0 hπ d
  have hG : IsUnit G.det := norm_grid_unit D hq hq₂ h0 hπ hMax d hd
  have hMul : G⁻¹*G=1 := Matrix.nonsing_inv_mul G hG
  have he : (inferInstance : DecidableEq J)=Classical.decEq J := by
    funext i j
    exact Subsingleton.elim _ _
  have hOne : (1:Matrix J J O)=(letI := Classical.decEq J; (1:Matrix J J O)) :=
    congrArg (fun d => letI : DecidableEq J := d; (1:Matrix J J O)) he
  exact ⟨G⁻¹,hMul.trans hOne⟩

include hMax in
/-- A genuine lower-triangular orientation of the native active rows. -/
theorem grid_has_left :
    letI := Classical.decEq I
    ∃ A : Matrix I I O, A * normalGrid D hq hq₂ h0 hπ s P = 1 := by
  letI : LinearOrder I := indexOrder q P s.depth
  exact abstract_grid_left D hq hq₂ h0 hπ hMax deg (fun i j h => index_order_le i j h)

include hMax in
noncomputable def gridSplit : Split π (matrixImage (rawGrid D hq s P)) I := by
  let e := grid_has_left D hq hq₂ h0 hπ s P hMax
  exact matrixSplit π (rawGrid D hq s P) (normalGrid D hq hq₂ h0 hπ s P)
    (Classical.choose e) ord (Classical.choose_spec e) (grid_factor D hq hq₂ h0 hπ s P)

variable [IsPrincipalIdealRing O]

local notation "SM" => matrixPowered π hMax (rawGrid D hq s P)
local notation "S" => (SM).2

include hq₂ h0 hπ in
theorem scalar_grid_profile (b : ℕ) :
    Fintype.card {j : Fin (SM).1 // (S).exponent j≤b} =
      Fintype.card {j : I // ord j≤b} :=
  same_exponent_profile (fromSmith S) (gridSplit D hq hq₂ h0 hπ s P hMax) hπ hMax b

include hq₂ h0 hπ in
theorem scalar_grid_capacity (hp : 0<P) :
    Fintype.card (Active S P)=Nat.card (S2Raw q P s.depth) := by
  let e₁ : Active S P ≃ {j : Fin (SM).1 // (S).exponent j≤P-1} :=
    { toFun := fun i => ⟨i.val,by have h := i.property; change (S).exponent i.val<P at h; omega⟩
      invFun := fun i => ⟨i.val,by have h := i.property; change (S).exponent i.val<P; omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : {j : I // ord j≤P-1} ≃ I :=
    { toFun := Subtype.val
      invFun := fun j => ⟨j,by have h := j.property; change ord j<P at h; change ord j≤P-1; omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e₁,scalar_grid_profile D hq hq₂ h0 hπ s P hMax (P-1),
    Fintype.card_congr e₂,s2_is_exact_count q P hq s.depth]

#print axioms gridMessages_permitted
#print axioms grid_factor
#print axioms grid_has_left
#print axioms gridSplit
#print axioms scalar_grid_profile
#print axioms scalar_grid_capacity
end
end V8CapacityUnified.Scalar
