import V8CapacityUnifiedLocalViews
import V8CapacitySpecialAbsoluteUpper

/-! A3/J3 can actually be inserted in U7 on each declared local view.
A jet cannot be consumed by an arbitrary coefficient extraction/reinsertion
program under this certificate: the decoder is one integral polynomial
and one terminal top readout with the specified output loss. -/
namespace V8CapacityUnified.U7
open scoped Classical BigOperators
open V8CapacityCRTJet V8CapacityNativeA3 V8CapacityNativeMatrix
open V8CapacityMonicBasis V8CapacityWidthGrid V8CapacityActiveWitness
open V8CapacityWidthRank V8CapacitySpecialAbsoluteUpper V8CapacitySymbolic

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1450000

variable {O K H : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [IsPrincipalIdealRing O]
variable [Field K] [Algebra O K] [IsFractionRing O K] [Fintype H]
variable [Fintype (IsLocalRing.ResidueField O)]
variable {π : O} {q : ℕ} (D : V8CapacityDigits.Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (L k : ℕ)

local notation "P" => (L+1)
local notation "κ" => IsLocalRing.ResidueField O
local notation "E" => Digits H k
local notation "rows" => Grid H P k
local notation "cols" => Columns H π P k
local notation "CM" => monicC π P k D hq
local notation "deg" => (@rowDegree E _ (DegreeCap P k))
local notation "SM" => actualSmith hMax q deg (CM : Matrix rows cols O)
local notation "JIdx" => Index SM L 1 (H → κ)

def nativeJetDecode (π : O) (L k : ℕ) (u : H → Jet O k)
    (c : MvPolynomial H (Jet O k)) : K :=
  algebraMap O K (origNumerator k u c) / (algebraMap O K (π^L))

include hq₂ h0 hπ in
/-- This uses the true all-residue A2 Smith width, not a large-field
coefficient count. The output is a matrix in the fraction field. -/
theorem A2_bipartite (hk : 0<k) (d : κ → O)
    (hd : Function.RightInverse d (IsLocalRing.residue O)) :
    bipartite π (nativeJetDecode (K:=K) (H:=H) π L k) (Fintype.card JIdx) := by
  intro A Y _ _ u c
  obtain ⟨l,r,h⟩ := actual_K_upper (K:=K) D hq hq₂ h0 hπ hMax L 1 k hk
    (by decide) d hd u c
  refine ⟨Matrix.of (fun a y => ∑ i : JIdx, l a i*r i y),separated_sum_rank l r,?_⟩
  intro a y
  simpa only [nativeJetDecode,Matrix.of_apply,pow_one] using h a y

include D hq hq₂ h0 hπ hMax in
/-- Large-residue/closed-count bound, still valid as an upper bound
when q is small; no claim of equality for those small q. -/
theorem J3_bipartite (hk : 0<k) (e : Fin q ≃ κ)
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O)) :
    bipartite π (nativeJetDecode (K:=K) (H:=H) π L k)
      (q^(Fintype.card H)*Fintype.card cols) := by
  intro A Y _ _ u c
  obtain ⟨a,ha,h⟩ := unrestricted_J3_upper (K:=K) D hq hq₂ h0 hπ hMax L 1 k hk
    (by decide) e d hd u c
  refine ⟨a,ha,fun a y => ?_⟩
  simpa only [nativeJetDecode,pow_one] using h a y

#print axioms A2_bipartite
#print axioms J3_bipartite
end
end V8CapacityUnified.U7
