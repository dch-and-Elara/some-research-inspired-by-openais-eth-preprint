import V8CapacityUnifiedScalarGrid
import V8CapacityUnifiedScalarUpper

/-! The paper's literal S3 receivers at the original S2 active
sender tuples. Same actual quotient image as all attainable columns
on this grid, not merely the right cardinality. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators
open V8CapacityDigits V8CapacitySmith V8CapacityCRTJet
open V8CapacitySpecialSplit V8CapacityUnified

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1650000

variable {O H : Type*} [CommRing O] [IsDomain O] [Fintype H]
variable [IsLocalRing O] [IsPrincipalIdealRing O]
variable {π : O} {q : ℕ} (D : Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (s : PublicClass (O:=O) (H:=H)) (L p : ℕ)

local notation "P" => (L+p)
local notation "I" => S2Index q P s.depth
local notation "deg" => (indexDegree (q:=q) («P»:=P) (v:=s.depth))
local notation "wgt" => (fun j : I => weight q s.depth (deg j))
local notation "G" => normalGrid D hq hq₂ h0 hπ s P
local notation "A" => rawGrid D hq s P
local notation "E" => matrixImage A

def S3_receiver (j : I) : MvPolynomial H O :=
  MvPolynomial.C (π^(L-wgt j))*phi D hq s (deg j)

def S3_matrix : Matrix I I O :=
  Matrix.of fun r j => π^(wgt j-L)*G r j

theorem S3_native_equality (r j : I) :
    MvPolynomial.eval (gridMessages D hq s P r) (S3_receiver D hq s L p j)
      =π^L*S3_matrix D hq hq₂ h0 hπ s L p r j := by
  simp only [S3_receiver,map_mul,MvPolynomial.eval_C,gridMessages,phi_eval_normalized D hq hq₂ h0 hπ]
  change π^(L-wgt j)*(π^wgt j*G r j)=π^L*(π^(wgt j-L)*G r j)
  have he : (L-wgt j)+wgt j=L+(wgt j-L) := by omega
  rw [← mul_assoc,← mul_assoc,← pow_add,← pow_add,he]

include hMax in
/-- Every attainable integral lift on the native grid reduces to an
actual linear combination of S3's concrete output columns. -/
theorem S3_spans_attained (v : I → O) (hv : realizable π L p E v) :
    ∃ c : I → O, residueRows π p ((S3_matrix D hq hq₂ h0 hπ s L p).mulVec c)=residueRows π p v := by
  obtain ⟨δ,hδ⟩ := hv
  let z : I → O := v+(π^p:O)•δ
  let sp := gridSplit D hq hq₂ h0 hπ s P hMax
  have hz := (sat_iff sp hπ L z).mp hδ
  choose c hc using hz.2
  refine ⟨c,?_⟩
  have hcoord (j : I) : sp.proj z j=π^(wgt j-L)*c j := hc j
  have hEq : (S3_matrix D hq hq₂ h0 hπ s L p).mulVec c=z := by
    calc
      _ = sp.embed (sp.proj z) := by
        change (S3_matrix D hq hq₂ h0 hπ s L p).mulVec c= (G).mulVec (sp.proj z)
        funext r
        simp only [Matrix.mulVec,dotProduct,S3_matrix,Matrix.of_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [hcoord j]
        ring
      _ = z := hz.1
  rw [hEq]
  funext r
  simp only [residueRows_apply]
  apply (residues_eq_iff π p _ _).mpr
  refine ⟨δ r,?_⟩
  change v r+π^p*δ r-v r=_
  ring

#print axioms S3_native_equality
#print axioms S3_spans_attained
end
end V8CapacityUnified.Scalar
