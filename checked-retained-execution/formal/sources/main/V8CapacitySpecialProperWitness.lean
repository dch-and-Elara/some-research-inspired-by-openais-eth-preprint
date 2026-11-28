import V8CapacitySpecialProperCapacity
import V8CapacityActiveWitness

/-! A fixed proper image has an attainable lower witness using only
its actual original rows. There are no assumed extra grid rows. -/
namespace V8CapacitySpecialProperCapacity
open scoped Classical BigOperators
open V8CapacityCRTJet V8CapacitySmith
open V8CapacityWidthUpper V8CapacityActiveWitness V8CapacitySpecialImageSpan

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {O H Z : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [IsPrincipalIdealRing O] [Fintype Z] [Fintype H] [Nonempty Z] {k : ℕ}
variable [Nontrivial (Jet O k)] {π : O}
variable (U : Z → H → Jet O k)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (L p : ℕ)

local notation "S" => actualProperSmith U π hMax
local notation "Act" => Active S (L+p)
local notation "Idx" => Index S L p Unit
local notation "B" => BaseMod O π p

def properReadCoord : (Z → O) →ₗ[O] (Idx → O) where
  toFun x := fun j => coord S x ((S).chart.f j.2)
  map_add' u v := by funext i; simp [coord]
  map_smul' t u := by funext i; simp [coord]

def properReceive : (Z → B) →ₗ[B] (Idx → B) :=
  ((LinearMap.toMatrix' (properReadCoord U hMax L p)).map (coeffMod O π p)).mulVecLin

theorem actual_proper_receipt (x : Z → O) (j : Idx) :
    properReceive U hMax L p (fun i => coeffMod O π p (x i)) j =
      coeffMod O π p (coord S x ((S).chart.f j.2)) := by
  change ((LinearMap.toMatrix' (properReadCoord U hMax L p)).map (coeffMod O π p)).mulVec
    ((coeffMod O π p) ∘ x) j=_
  rw [← RingHom.map_mulVec,LinearMap.toMatrix'_mulVec]
  rfl

/-- The same one set of original receiver columns works against
every candidate coefficient-ring factorization width on Z. -/
theorem exact_proper_width (hk : 0<k) (hπ : π≠0) (hp : 0<p) :
    ∃ decoder : Idx → MvPolynomial H (Jet O k),
    ∃ out : Idx → Z → O,
      (∀ j z, π^(L+p)∣readFinite U (decoder j) z-π^L*out j z) ∧
      ∀ n : ℕ, ∀ fac : (Fin n → B) →ₗ[B] (Z → B),
        (∀ j, ∃ c, fac c=fun z => coeffMod O π p (out j z)) → Fintype.card Act≤ n := by
  have lift (j : Idx) := embed_realizable S hπ L p (basisDigit S L p j)
  choose v hv he using lift
  let out (j : Idx) : Z → O := v j ()
  have hsource (j : Idx) : ∃ g : MvPolynomial H (Jet O k), ∀ z,
      π^(L+p)∣readFinite U g z-π^L*out j z :=
    (exact_proper_saturation U hk L p (out j)).mpr (hv j ())
  choose decoder hd using hsource
  refine ⟨decoder,out,hd,fun n fac hfac => ?_⟩
  have hz : IsLocalRing.residue O π=0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (by rw [hMax,Ideal.mem_span_singleton])
  have hgen (j : Idx) :
      properReceive U hMax L p (fun z => coeffMod O π p (out j z)) =
        embed S hπ L p (basisDigit S L p j) := by
    funext i
    rw [actual_proper_receipt U hMax L p]
    have h : i.1=() := Subsingleton.elim _ _
    simpa only [out,h] using he j i
  have bound := witness_requires_width S hπ L p hp hz (properReceive U hMax L p)
    (fun j z => coeffMod O π p (out j z)) hgen fac hfac
  simpa [Fintype.card_prod] using bound

#print axioms actual_proper_receipt
#print axioms exact_proper_width
end
end V8CapacitySpecialProperCapacity

