import V8CapacitySpecialJ6
import V8CapacitySpecialJ6Source
import V8CapacitySpecialLargeCapacity

/-! Assembly of the closed residue-precision J6 count for k≤q. The
summation is over the finite exponent box, with all high total degrees
contributing zero. This is the manuscript's sum over 0<|alpha|<k. -/
namespace V8CapacitySpecialJ6
open scoped Classical BigOperators
open Polynomial V8CapacityFeatures V8CapacitySymbolic V8CapacityNativeMatrix
open V8CapacityFeatureSpan V8CapacityWidthUpper V8CapacityMonicBasis V8CapacitySmith
open V8CapacityIntegrated V8CapacitySpecialJ6Source V8CapacitySpecialLargeCapacity

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {H K : Type*} [Fintype H] [Field K]

theorem zero_alpha_count (k : ℕ) (hk : 0<k) :
    Fintype.card { j : Fin k // feature (0:K) k (0:H→ℕ) j.val≠0}=1 := by
  have hj (j : Fin k) : feature (0:K) k (0:H→ℕ) j.val≠0 ↔ j.val=0 := by
    unfold feature rawFeature
    by_cases h : j.val=0
    · simp [h]
    · simp [h,Polynomial.coeff_one]
  let t : {j : Fin k // feature (0:K) k (0:H→ℕ) j.val≠0} :=
    ⟨⟨0,hk⟩,(hj ⟨0,hk⟩).mpr rfl⟩
  let e : {j : Fin k // feature (0:K) k (0:H→ℕ) j.val≠0} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => t
      left_inv := fun j => Subtype.ext (Fin.ext ((hj j.val).mp j.property).symm)
      right_inv := fun _ => rfl }
  simpa using Fintype.card_congr e

variable (c : ℕ) [Fact c.Prime]

def J6Term (k : ℕ) (a : H → ℕ) : ℕ :=
  if ha : a=0 then 1 else
    if (∑ e : H, a e)<k then
      1+(k-1-(∑ e : H, a e))/commonPower c a ha else 0

theorem all_alpha_count (k : ℕ) (hk : 0<k) [CharP K c]
    [ExpChar (MvPolynomial (Digits H k) K) c] (a : H → ℕ) :
    Fintype.card {j : Fin k // feature (0:K) k a j.val≠0}=J6Term c k a := by
  unfold J6Term
  split_ifs with h0 hsum
  · subst a
    exact zero_alpha_count (K:=K) k hk
  · exact exact_count_nonzero_alpha (K:=K) c a h0 hsum
  · haveI : IsEmpty {j : Fin k // feature (0:K) k a j.val≠0} := by
      constructor
      intro j
      exact j.property (V8CapacitySpecialFrobenius.feature_below_order_zero a j.val (by
        have hj := j.val.isLt
        omega))
    exact Fintype.card_eq_zero

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [IsPrincipalIdealRing O]

local notation "κ" => IsLocalRing.ResidueField O

def activeJ6Equiv (π : O) (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) (k : ℕ) :
    Columns H π 1 k ≃
      Σ a : ExponentBox H (DegreeCap 1 k),
        {j : Fin k // feature (0:κ) k (fun i => (a i).val) j.val≠0} where
  toFun i := ⟨i.val.1,⟨i.val.2,(active_iff_zero_constant π hMax k i.val).mp i.property⟩⟩
  invFun w := ⟨(w.1,w.2.val),(active_iff_zero_constant π hMax k (w.1,w.2.val)).mpr w.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem columns_J6_exact (π : O)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (k : ℕ) (hk : 0<k) [CharP κ c] [ExpChar (MvPolynomial (Digits H k) κ) c] :
    Fintype.card (Columns H π 1 k)=
      ∑ a : ExponentBox H (DegreeCap 1 k), J6Term c k (fun i => (a i).val) := by
  rw [Fintype.card_congr (activeJ6Equiv π hMax k),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  exact all_alpha_count (K:=κ) c k hk _

variable [Fintype (IsLocalRing.ResidueField O)]
variable {π : O} {q : ℕ} (D : V8CapacityDigits.Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (k : ℕ) [CharP (IsLocalRing.ResidueField O) c]
variable [ExpChar (MvPolynomial (Digits H k) (IsLocalRing.ResidueField O)) c]

local notation "E" => Digits H k
local notation "Rows" => Grid H 1 k
local notation "J" => Columns H π 1 k
local notation "rdeg" => (@rowDegree E _ (DegreeCap 1 k))
local notation "CM" => monicC π 1 k D hq
local notation "M" => weighted π q rdeg (CM : Matrix Rows J O)

include hq₂ h0 hπ in
theorem printed_J6_value (hk : 0<k) (hkq : k≤q) (e : Fin q ≃ κ) :
    Fintype.card ((H → κ) × Active (matrixPowered π hMax M).2 1) =
      q^(Fintype.card H)* (∑ a : ExponentBox H (DegreeCap 1 k), J6Term c k (fun i => (a i).val)) := by
  have hl : DegreeCap 1 k<q := by unfold DegreeCap; omega
  rw [capacity_formula D hq hq₂ h0 hπ hMax k 1 hk (by decide) hl e,
    columns_J6_exact c π hMax k hk]

#print axioms zero_alpha_count
#print axioms all_alpha_count
#print axioms activeJ6Equiv
#print axioms columns_J6_exact
#print axioms printed_J6_value
end
end V8CapacitySpecialJ6

