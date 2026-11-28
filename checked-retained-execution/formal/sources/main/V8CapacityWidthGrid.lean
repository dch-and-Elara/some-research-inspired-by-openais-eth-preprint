import V8CapacityActiveWitness
import V8CapacityIntegrated

/-! A3 attainment on the actual finite Newton evaluation grid, for a
given monic Newton coefficient matrix. The readback is a matrix over
the residue ring built from the inverse of the proven unit grid. -/
namespace V8CapacityWidthGrid
open scoped Classical BigOperators
open V8CapacityFactorial V8CapacityDigits V8CapacityNewtonGrid V8CapacitySmith
open V8CapacityIntegrated V8CapacityWidthUpper V8CapacityActiveWitness V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {O E I C F J : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [IsPrincipalIdealRing O]
variable [Fintype E] [Fintype I] [Fintype C] [Fintype F] [Fintype J] [LinearOrder I]
variable {π : O} {q : ℕ}
variable (D : Digits π q) (hq : 0<q) (hq₂ : 2≤q)
variable (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (degree : I → E → ℕ)
variable (order : ∀ i j, (∀ e, degree i e≤degree j e) → i≤j)

abbrev actualSmith (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (q : ℕ) (degree : I → E → ℕ) (N : Matrix I C O) :=
  (matrixPowered π hMax (weighted π q degree N)).2

variable (C₀ : Matrix I C O) (L p : ℕ)

local notation "S" => actualSmith hMax q degree C₀
local notation "Act" => Active S (L+p)
local notation "AIndex" => Index S L p F
local notation "B" => BaseMod O π p

def smithCoord : (I → O) →ₗ[O] (Act → O) where
  toFun x := fun i => coord S x ((S).chart.f i)
  map_add' x y := by ext i; simp [coord]
  map_smul' a x := by ext i; simp [coord]

def backMat : Matrix Act I O :=
  LinearMap.toMatrix' ((smithCoord hMax degree C₀ L p).comp
    ((normGrid D hq hq₂ h0 hπ degree)⁻¹).mulVecLin)

def gridReceive : ((F × I) → B) →ₗ[B] (AIndex → B) :=
  LinearMap.pi fun i =>
    ((LinearMap.proj i.2).comp ((backMat D hq hq₂ h0 hπ hMax degree C₀ L p).map
      (coeffMod O π p)).mulVecLin).comp
      (LinearMap.pi fun j => LinearMap.proj (i.1,j))

def gridColumn (v : F → I → O) : (F × I) → O :=
  fun i => (normGrid D hq hq₂ h0 hπ degree).mulVec (v i.1) i.2

include order in
theorem actual_grid_receipt (v : F → I → O) (i : AIndex) :
    gridReceive D hq hq₂ h0 hπ hMax degree C₀ L p
      (fun j => coeffMod O π p (gridColumn D hq hq₂ h0 hπ degree v j)) i =
    coeffMod O π p (coord S (v i.1) ((S).chart.f i.2)) := by
  let W := normGrid D hq hq₂ h0 hπ degree
  have hu := norm_grid_unit D hq hq₂ h0 hπ hMax degree order
  change ((backMat D hq hq₂ h0 hπ hMax degree C₀ L p).map (coeffMod O π p)).mulVec
    ((coeffMod O π p) ∘ W.mulVec (v i.1)) i.2 = _
  rw [← RingHom.map_mulVec]
  unfold backMat
  simp only [LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
  rw [show ((W⁻¹).mulVecLin (W.mulVec (v i.1)))=v i.1 by
    change (W⁻¹).mulVec (W.mulVec (v i.1))=_
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul W hu,Matrix.one_mulVec]
    ]
  rfl

include order in
/-- All desired generators have actual grid-valued outputs. Each column
has an integral source coefficient combination on its separate fiber
whose raw numerator agrees there and on the entire unbounded chart.
The CRT lemma is the independent bridge for packing these combinations
in one source jet polynomial. -/
theorem actual_grid_generators :
    ∃ out : AIndex → F → I → O,
      (∀ j f, ∃ a : C → O, ∀ x : E → O, π^(L+p)∣
        rawAt D hq degree C₀ a x-π^L*evalNormalized D hq hq₂ h0 hπ degree (out j f) x) ∧
      (∀ j, gridReceive D hq hq₂ h0 hπ hMax degree C₀ L p
        (fun i => coeffMod O π p (gridColumn D hq hq₂ h0 hπ degree (out j) i))=
          embed S hπ L p (basisDigit S L p j)) := by
  have R (j : AIndex) := embed_realizable S hπ L p (basisDigit S L p j)
  choose v hv he using R
  refine ⟨v,?_,?_⟩
  · intro j f
    exact (exact_readability D hq hq₂ h0 hπ hMax degree order C₀ L p (v j f)).mpr (hv j f)
  · intro j
    funext i
    rw [actual_grid_receipt D hq hq₂ h0 hπ hMax degree order C₀ L p]
    exact he j i

include order in
/-- The finite Newton grid achieves the capacity lower bound against all
R_p width factorizations. Includes input sets of all residue words via F. -/
theorem attained_grid_width (hp : 0<p) (hz : IsLocalRing.residue O π=0) :
    ∃ out : AIndex → F → I → O,
      (∀ j f, ∃ a : C → O, ∀ x : E → O, π^(L+p)∣
        rawAt D hq degree C₀ a x-π^L*evalNormalized D hq hq₂ h0 hπ degree (out j f) x) ∧
      ∀ (fac : (J → B) →ₗ[B] ((F × I) → B)),
        (∀ j, ∃ c, fac c=fun i => coeffMod O π p
          (gridColumn D hq hq₂ h0 hπ degree (out j) i)) →
          Fintype.card AIndex≤Fintype.card J := by
  obtain ⟨v,hv,he⟩ := actual_grid_generators D hq hq₂ h0 hπ hMax degree order C₀ L p (F:=F)
  refine ⟨v,hv,fun fac hfac => ?_⟩
  exact witness_requires_width S hπ L p hp hz
    (gridReceive D hq hq₂ h0 hπ hMax degree C₀ L p)
    (fun j i => coeffMod O π p (gridColumn D hq hq₂ h0 hπ degree (v j) i)) he fac hfac

#print axioms actual_grid_receipt
#print axioms actual_grid_generators
#print axioms attained_grid_width
end
end V8CapacityWidthGrid

