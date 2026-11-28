import V8CapacityNativeA3Witness
import V8CapacityWidthRank

/-! Exact largest minimum ordinary K-rank for integral lifts of A1,
in addition to the worst-case R_p width result. -/
namespace V8CapacityNativeA3
open scoped Classical BigOperators
open V8CapacitySymbolic V8CapacityJetChart V8CapacityCRTJet
open V8CapacityNativeMatrix V8CapacityMonicBasis V8CapacityIntegrated
open V8CapacityWidthGrid V8CapacityWidthUpper V8CapacityActiveWitness V8CapacityWidthRank

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000

variable {O K H A Y : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [IsPrincipalIdealRing O] [Fintype H] [Fintype (IsLocalRing.ResidueField O)]
variable [Field K] [Algebra O K] [IsFractionRing O K] [Fintype A] [Fintype Y]
variable {π : O} {q : ℕ}
variable (D : V8CapacityDigits.Digits π q) (hq : 0<q) (hq₂ : 2≤q)
variable (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (L p k : ℕ)

local notation "κ" => IsLocalRing.ResidueField O
local notation "F" => (H → κ)
local notation "P" => (L+p)
local notation "E" => Digits H k
local notation "I" => Grid H P k
local notation "rdeg" => (@rowDegree E _ (DegreeCap P k))
local notation "CM" => monicC π P k D hq
local notation "SR" => actualSmith hMax q rdeg CM
local notation "IndexType" => Index SR L p F

include hq₂ h0 hπ in
theorem integral_rank_upper (hk : 0<k) (hp : 0<p)
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (U : A → H → Jet O k) (recv : Y → MvPolynomial H (Jet O k)) (target : Matrix A Y O)
    (congruent : ∀ a y, π^P∣origNumerator k (U a) (recv y)-π^L*target a y) :
    ∃ b : Matrix A Y O, b.map (coeffMod O π p)=target.map (coeffMod O π p) ∧
      (b.map (algebraMap O K)).rank≤ Fintype.card IndexType := by
  obtain ⟨l,r,h⟩ := actual_K_upper (K:=K) D hq hq₂ h0 hπ hMax L p k hk hp d hd U recv
  apply integral_congruent_low_rank π p target l r
  intro a y
  obtain ⟨e,he⟩ := h a y
  obtain ⟨v,hv⟩ := divided_diff (K:=K) hπ L p _ _ (congruent a y)
  have hne : algebraMap O K (π^L)≠0 :=
    fun h => (pow_ne_zero _ hπ) ((IsFractionRing.injective O K) (h.trans (map_zero _).symm))
  have hval : algebraMap O K (π^L*target a y)/(algebraMap O K (π^L)) =
      algebraMap O K (target a y) := by rw [map_mul]; field_simp
  rw [hval] at hv
  refine ⟨e-v,?_⟩
  rw [mul_sub,map_sub]
  linear_combination he-hv

include hq₂ h0 hπ in
/-- On one actual finite Newton witness, the least ordinary K-rank
among *all* integral lifts reaches the same exact A3 number. -/
theorem exact_integral_rank_witness (hk : 0<k) (hp : 0<p)
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O)) :
    ∃ decoder : IndexType → MvPolynomial H (Jet O k),
    ∃ a : Matrix (F × I) IndexType O,
      (∀ x j, π^P∣origNumerator k (nativeGrid D hq L p k d x) (decoder j)-π^L*a x j) ∧
      (∀ b : Matrix (F × I) IndexType O,
        b.map (coeffMod O π p)=a.map (coeffMod O π p) →
          Fintype.card IndexType≤ (b.map (algebraMap O K)).rank) ∧
      ∃ b : Matrix (F × I) IndexType O,
        b.map (coeffMod O π p)=a.map (coeffMod O π p) ∧
          (b.map (algebraMap O K)).rank=Fintype.card IndexType := by
  obtain ⟨decoder,out,ho,hbound⟩ := exact_width_witness (H:=H) D hq hq₂ h0 hπ hMax L p k hk hp d hd
  let a : Matrix (F × I) IndexType O := Matrix.of fun x j => out j x
  have ha (x : F × I) (j : IndexType) :
      π^P∣origNumerator k (nativeGrid D hq L p k d x) (decoder j)-π^L*a x j := ho j x
  have lower (b : Matrix (F × I) IndexType O)
      (hb : b.map (coeffMod O π p)=a.map (coeffMod O π p)) :
      Fintype.card IndexType≤ (b.map (algebraMap O K)).rank := by
    obtain ⟨n,hn,l,r,he⟩ := residue_factor_of_krank (K:=K) π p b
    have hfac (j : IndexType) : ∃ c, l.mulVecLin c=fun i => coeffMod O π p (out j i) := by
      refine ⟨fun t => r t j,?_⟩
      funext i
      have h := congrFun (congrFun (he.symm.trans hb) i) j
      exact h
    exact (hbound n l.mulVecLin hfac).trans hn
  refine ⟨decoder,a,ha,lower,?_⟩
  obtain ⟨b,hb,hb₁⟩ := integral_rank_upper (K:=K) D hq hq₂ h0 hπ hMax L p k hk hp d hd
    (nativeGrid D hq L p k d) decoder a ha
  exact ⟨b,hb,le_antisymm hb₁ (lower b hb)⟩

#print axioms integral_rank_upper
#print axioms exact_integral_rank_witness
end
end V8CapacityNativeA3

