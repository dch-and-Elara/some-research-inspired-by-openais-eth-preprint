import V8CapacitySpecialLargeCapacity

/-! The exact original J3 theorem over all finite sender and receiver
sets when q>D. The upper bound uses actual unrestricted integral source
polynomials and the witness uses the same literal native jet domain. -/
namespace V8CapacitySpecialNativeLarge
open scoped Classical BigOperators
open V8CapacitySymbolic V8CapacityNativeMatrix V8CapacityMonicBasis
open V8CapacityIntegrated V8CapacitySmith V8CapacityWidthGrid
open V8CapacityWidthUpper V8CapacityActiveWitness V8CapacityNativeA3
open V8CapacityWidthRank V8CapacityCRTJet V8CapacitySpecialLargeCapacity

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000

variable {O K H A Y : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [IsPrincipalIdealRing O] [Fintype H] [Fintype (IsLocalRing.ResidueField O)]
variable [Field K] [Algebra O K] [IsFractionRing O K] [Fintype A] [Fintype Y]
variable {π : O} {q : ℕ} (D : V8CapacityDigits.Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (L p k : ℕ)

local notation "κ" => IsLocalRing.ResidueField O
local notation "F" => (H → κ)
local notation "P" => (L+p)
local notation "E" => Digits H k
local notation "I" => Grid H P k
local notation "C" => Columns H π P k
local notation "rdeg" => (@rowDegree E _ (DegreeCap P k))
local notation "CM" => monicC π P k D hq
local notation "SR" => actualSmith hMax q rdeg CM
local notation "IndexType" => Index SR L p F
local notation "J3" => (q^(Fintype.card H)*Fintype.card C)

include hMax hq₂ h0 hπ in
theorem universal_integer_width (hk : 0<k) (hp : 0<p) (large : DegreeCap P k<q)
    (enumerate : Fin q ≃ κ) (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (U : A → H → Jet O k) (recv : Y → MvPolynomial H (Jet O k)) (target : Matrix A Y O)
    (congruent : ∀ a y, π^P∣origNumerator k (U a) (recv y)-π^L*target a y) :
    ∃ n≤J3, ∃ l : Matrix A (Fin n) (BaseMod O π p),
      ∃ r : Matrix (Fin n) Y (BaseMod O π p), target.map (coeffMod O π p)=l*r := by
  obtain ⟨b,hb,hr⟩ := integral_rank_upper (K:=FractionRing O) D hq hq₂ h0 hπ hMax L p k hk hp d hd U recv
    target congruent
  obtain ⟨n,hn,l,r,hfac⟩ := residue_factor_of_krank (K:=FractionRing O) π p b
  have hh : Fintype.card IndexType=J3 := capacity_formula D hq hq₂ h0 hπ hMax k P hk (by omega)
    large enumerate
  refine ⟨n,(hn.trans hr).trans_eq hh,l,r,?_⟩
  exact hb.symm.trans hfac

include hq₂ h0 hπ in
theorem exact_integer_lift_optimum (hk : 0<k) (hp : 0<p) (large : DegreeCap P k<q)
    (enumerate : Fin q ≃ κ) (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O)) :
    ∃ decoder : IndexType → MvPolynomial H (Jet O k),
    ∃ a : Matrix (F × I) IndexType O,
      (∀ x j, π^P∣origNumerator k (nativeGrid D hq L p k d x) (decoder j)-π^L*a x j) ∧
      (∀ b : Matrix (F × I) IndexType O,
        b.map (coeffMod O π p)=a.map (coeffMod O π p) →
          J3≤(b.map (algebraMap O K)).rank) ∧
      ∃ b : Matrix (F × I) IndexType O, b.map (coeffMod O π p)=a.map (coeffMod O π p) ∧
         (b.map (algebraMap O K)).rank=J3 := by
  have hh : Fintype.card IndexType=J3 := capacity_formula D hq hq₂ h0 hπ hMax k P hk (by omega)
    large enumerate
  rw [← hh]
  exact exact_integral_rank_witness (K:=K) (H:=H) D hq hq₂ h0 hπ hMax L p k hk hp d hd

#print axioms universal_integer_width
#print axioms exact_integer_lift_optimum
end
end V8CapacitySpecialNativeLarge

