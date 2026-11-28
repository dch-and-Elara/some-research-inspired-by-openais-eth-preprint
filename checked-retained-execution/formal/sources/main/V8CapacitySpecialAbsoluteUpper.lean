import V8CapacitySpecialNativeLarge

/-! J3 is an upper bound without the large-residue assumption.
Only its universal attainability uses q>D; the actual A2 rank can drop
at smaller q. No bound on the receiver circuit is needed. -/
namespace V8CapacitySpecialAbsoluteUpper
open scoped Classical BigOperators
open Module V8CapacitySymbolic V8CapacityNativeMatrix V8CapacityMonicBasis
open V8CapacityIntegrated V8CapacitySmith V8CapacityWidthGrid
open V8CapacityWidthUpper V8CapacityActiveWitness V8CapacityNativeA3
open V8CapacityWidthRank V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false

variable {O I J : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [IsPrincipalIdealRing O] [Fintype I] [Fintype J]

theorem cap_le_columns (π : O) (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (M : Matrix I J O) (P : ℕ) :
    Fintype.card (Active (matrixPowered π hMax M).2 P)≤Fintype.card J := by
  let T := matrixPowered π hMax M
  have hr := LinearMap.finrank_range_le M.mulVecLin
  have he := Module.finrank_eq_card_basis T.2.chart.bN
  rw [he,Module.finrank_fintype_fun_eq_card] at hr
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans hr

variable {K H A Y : Type*} [Fintype H] [Fintype A] [Fintype Y]
variable [Fintype (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
variable {π : O} {q : ℕ} (D : V8CapacityDigits.Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (L p k : ℕ)

local notation "κ" => IsLocalRing.ResidueField O
local notation "P" => (L+p)
local notation "E" => Digits H k
local notation "Rows" => Grid H P k
local notation "JCOL" => Columns H π P k
local notation "rdeg" => (@rowDegree E _ (DegreeCap P k))
local notation "CM" => monicC π P k D hq
local notation "S" => actualSmith hMax q rdeg CM
local notation "IndexType" => Index S L p (H → κ)
local notation "J3" => (q^(Fintype.card H)*Fintype.card JCOL)

include hMax hq₂ h0 hπ in
theorem unrestricted_J3_upper (hk : 0<k) (hp : 0<p)
    (enumerate : Fin q ≃ κ) (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (U : A → H → Jet O k) (recv : Y → MvPolynomial H (Jet O k)) :
    ∃ a : Matrix A Y K, a.rank≤J3 ∧
      ∀ x y, ∃ e : O, (algebraMap O K (origNumerator k (U x) (recv y)))/
        (algebraMap O K (π^L))-a x y=algebraMap O K (π^p*e) := by
  obtain ⟨l,r,h⟩ := actual_K_upper (K:=K) D hq hq₂ h0 hπ hMax L p k hk hp d hd U recv
  have count : Fintype.card IndexType≤J3 := by
    rw [active_cardinality D hq hMax L p k enumerate]
    exact Nat.mul_le_mul_left _ (cap_le_columns π hMax (weighted π q rdeg CM : Matrix Rows JCOL O) P)
  exact ⟨Matrix.of fun x y => ∑ i, l x i*r i y,(separated_sum_rank l r).trans count,h⟩

#print axioms cap_le_columns
#print axioms unrestricted_J3_upper
end
end V8CapacitySpecialAbsoluteUpper

