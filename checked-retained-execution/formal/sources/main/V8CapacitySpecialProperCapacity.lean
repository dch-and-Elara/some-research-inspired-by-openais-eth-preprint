import V8CapacitySpecialImageExact
import V8CapacityNativeA3
import V8CapacityWidthRank

/-! A finite prescribed image needs its own exact projected matrix.
All numerator congruences, saturation and fraction-field width below
come from that literal matrix, even if it has deficient free rank. -/
namespace V8CapacitySpecialProperCapacity
open scoped Classical BigOperators
open V8CapacityCRTJet V8CapacitySmith V8CapacityWidthUpper
open V8CapacitySpecialImageSpan V8CapacityNativeA3 V8CapacityWidthRank

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {O K H Z Y : Type*}
variable [CommRing O] [IsDomain O] [IsLocalRing O] [IsPrincipalIdealRing O]
variable [Field K] [Algebra O K] [IsFractionRing O K]
variable [Fintype Z] [Fintype H] [Fintype Y] [Nonempty Z] {k : ℕ}
variable [Nontrivial (Jet O k)] {π : O}

def readFinite (U : Z → H → Jet O k) (F : MvPolynomial H (Jet O k)) (z : Z) :=
  coefficient O k (k-1) (readJet U F z)

theorem exact_proper_saturation (U : Z → H → Jet O k) (hk : 0<k)
    (L p : ℕ) (v : Z → O) :
    (∃ F : MvPolynomial H (Jet O k), ∀ z, π^(L+p)∣readFinite U F z-π^L*v z) ↔
      realizable π L p (matrixImage (finiteRaw U)) v := by
  constructor
  · rintro ⟨F,hF⟩
    choose Δ hΔ using hF
    refine ⟨Δ,(exact_projected_image U hk _).mpr ⟨F,?_⟩⟩
    intro z
    change readFinite U F z=π^L*(v z+π^p*Δ z)
    have h := hΔ z
    rw [pow_add] at h
    linear_combination h
  · rintro ⟨Δ,hΔ⟩
    obtain ⟨F,hF⟩ := (exact_projected_image U hk _).mp hΔ
    refine ⟨F,fun z => ⟨Δ z,?_⟩⟩
    change readFinite U F z-π^L*v z=π^(L+p)*Δ z
    have hz := hF z
    change readFinite U F z=π^L*(v z+π^p*Δ z) at hz
    rw [hz,pow_add]
    ring

abbrev actualProperSmith (U : Z → H → Jet O k) (π : O)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) :=
  (matrixPowered π hMax (finiteRaw U)).2

theorem proper_fraction_bound (U : Z → H → Jet O k) (hk : 0<k)
    (hπ : π≠0) (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) (L p : ℕ)
    (recv : Y → MvPolynomial H (Jet O k)) :
    ∃ l : Z → Active (actualProperSmith U π hMax) (L+p) → K,
      ∃ r : Active (actualProperSmith U π hMax) (L+p) → Y → K,
        ∀ z y, ∃ e : O, (algebraMap O K (readFinite U (recv y) z))/(algebraMap O K (π^L))-
          (∑ i : Active (actualProperSmith U π hMax) (L+p), l z i*r i y)=algebraMap O K (π^p*e) := by
  let S := actualProperSmith U π hMax
  let col (_ : Unit) (y : Y) : matrixImage (finiteRaw U) :=
    ⟨readFinite U (recv y),in_finite_raw_span U hk (recv y)⟩
  obtain ⟨l,r,hr⟩ := separated_fraction_upper (S:=S) (K:=K) hπ L p
    (fun _ : Z => ()) (fun z => LinearMap.proj z) col
  refine ⟨fun z i => l z ((),i),fun i y => r ((),i) y,fun z y => ?_⟩
  obtain ⟨e,he⟩ := hr z y
  refine ⟨e,?_⟩
  rw [Fintype.sum_prod_type,Fintype.sum_unique] at he
  exact he

#print axioms exact_proper_saturation
#print axioms proper_fraction_bound
end
end V8CapacitySpecialProperCapacity

