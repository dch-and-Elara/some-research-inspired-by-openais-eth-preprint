import V8CapacityUnifiedScalarS3

/-! S2/S3 sharpness, with actual public classes and literal polynomial
receivers, over the quotient ring and for least rank of any integral
lift over the fraction field. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators
open V8CapacityDigits V8CapacityCRTJet V8CapacitySmith
open V8CapacityUnified V8CapacityWidthUpper V8CapacityWidthRank

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1700000

variable {O H : Type*} [CommRing O] [IsDomain O] [Fintype H]
variable [IsLocalRing O] [IsPrincipalIdealRing O]
variable {π : O} {q : ℕ} (D : Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (s : PublicClass (O:=O) (H:=H)) (L p : ℕ)

local notation "P" => (L+p)
local notation "I" => S2Index q P s.depth
local notation "B" => BaseMod O π p
local notation "C" => Nat.card (S2Raw q P s.depth)
local notation "M" => S3_matrix D hq hq₂ h0 hπ s L p
local notation "MR" => Matrix.map (M) (coeffMod O π p)
local notation "E" => matrixImage (rawGrid D hq s P)
local notation "S" => Sigma.snd (matrixPowered π hMax (rawGrid D hq s P))
local notation "Act" => Active S P

include hMax in
theorem S3_width_lower (hp : 0<p) (d : ℕ)
    (hFactor : factors π p (fun y x => MR x y) d) : C≤d := by
  obtain ⟨A,B₀,hM⟩ := hFactor
  have hh : MR=A*B₀ := hM
  obtain ⟨w,hw,hMin⟩ := U_width_exact p S L hπ hp hMax
  have hCol (j : Act) : ∃ c : Fin d → B, A.mulVec c=w j := by
    obtain ⟨v,hv⟩ := residueRows_surj π p (w j)
    have hmem : residueRows π p v∈attainable π L p E := by rw [hv]; exact hw j
    have hread : realizable π L p E v := (U1_lift π L p E v).mp hmem
    obtain ⟨co,hco⟩ := S3_spans_attained D hq hq₂ h0 hπ hMax s L p v hread
    have hRed : (MR).mulVec (residueRows π p co)=residueRows π p ((M).mulVec co) := by
      funext u
      change (MR).mulVec ((coeffMod O π p) ∘ co) u=_
      rw [← RingHom.map_mulVec]
      rfl
    refine ⟨B₀.mulVec (residueRows π p co),?_⟩
    rw [Matrix.mulVec_mulVec,← hh,hRed,hco,hv]
  choose z hz using hCol
  have hW : factors π p w d := by
    refine ⟨A,Matrix.of (fun t j => z j t),?_⟩
    ext x y
    exact (congrFun (hz y) x).symm
  have hN := scalar_grid_capacity D hq hq₂ h0 hπ s P hMax (by omega)
  exact hN ▸ hMin.2 hW

include hMax in
theorem S3_actual_minimum (hp : 0<p) :
    IsLeast {d : ℕ | factors π p (fun y x => MR x y) d} C := by
  have correct (x y : I) :
      π^P∣MvPolynomial.eval (gridMessages D hq s P x) (S3_receiver D hq s L p y)-π^L*M x y := by
    rw [S3_native_equality D hq hq₂ h0 hπ s L p,sub_self]
    exact dvd_zero _
  obtain ⟨d,hd,hF⟩ := S2_residue_width D hq hq₂ h0 hπ s L p
    (gridMessages D hq s P) (gridMessages_permitted D hq s P)
    (S3_receiver D hq s L p) M correct
  have he := le_antisymm hd (S3_width_lower D hq hq₂ h0 hπ hMax s L p hp d hF)
  refine ⟨he ▸ hF,fun d h => ?_⟩
  exact S3_width_lower D hq hq₂ h0 hπ hMax s L p hp d h

variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

include hMax in
theorem S3_any_integral_lift (hp : 0<p) (N : Matrix I I O) (hn : N.map (coeffMod O π p)=MR) :
    C≤(N.map (algebraMap O K)).rank := by
  obtain ⟨d,hd,a,b,he⟩ := residue_factor_of_krank (K:=K) π p N
  exact (S3_width_lower D hq hq₂ h0 hπ hMax s L p hp d
    ⟨a,b,hn.symm.trans he⟩).trans hd

include hMax in
theorem S3_minimum_K_rank (hp : 0<p) :
    ((M).map (algebraMap O K)).rank=C := by
  apply le_antisymm _ (S3_any_integral_lift (K:=K) D hq hq₂ h0 hπ hMax s L p hp M rfl)
  rw [← s2_is_exact_count q P hq s.depth]
  exact Matrix.rank_le_card_width _

#print axioms S3_width_lower
#print axioms S3_actual_minimum
#print axioms S3_any_integral_lift
#print axioms S3_minimum_K_rank
end
end V8CapacityUnified.Scalar
