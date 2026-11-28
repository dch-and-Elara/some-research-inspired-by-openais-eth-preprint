import V8CapacityNativeA3

/-! Faithful finite witness for the exact worst-case integral A3 width.
The logical decoder is assembled by actual CRT in the original source
jet polynomial ring, not passed as a modeling assumption. -/
namespace V8CapacityNativeA3
open scoped Classical BigOperators
open V8CapacitySymbolic V8CapacityJetChart V8CapacityCRTJet
open V8CapacityNativeMatrix V8CapacityNativeCRT V8CapacityIntegrated
open V8CapacityMonicBasis V8CapacityGridOrder V8CapacityNewtonGrid V8CapacitySmith
open V8CapacityWidthGrid V8CapacityWidthUpper V8CapacityActiveWitness

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000

variable {O H : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [IsPrincipalIdealRing O] [Fintype H] [Fintype (IsLocalRing.ResidueField O)]
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
local notation "C" => Columns H π P k
local notation "rdeg" => (@rowDegree E _ (DegreeCap P k))
local notation "CM" => monicC π P k D hq
local notation "SR" => actualSmith hMax q rdeg CM
local notation "IndexType" => Index SR L p F
local notation "B" => BaseMod O π p

def nativeGrid (d : κ → O) (i : F × I) : H → Jet O k :=
  sourceInput π k d i.1 (nodeAt D hq rdeg i.2)

include hq₂ h0 hπ in
/-- Independent of any proposed width r, this one finite sender and
receiver family attains the true A3 capacity. The divisibility relation
also certifies that each constructed output is integral. -/
theorem exact_width_witness (hk : 0<k) (hp : 0<p)
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O)) :
    ∃ f : IndexType → MvPolynomial H (Jet O k),
    ∃ out : IndexType → F × I → O,
      (∀ j i, π^P ∣ origNumerator k (nativeGrid D hq L p k d i) (f j)-π^L*out j i) ∧
      (∀ r : ℕ, ∀ fac : (Fin r → B) →ₗ[B] ((F × I) → B),
        (∀ j, ∃ c, fac c=fun i => coeffMod O π p (out j i)) →
          Fintype.card IndexType≤ r) := by
  letI : LinearOrder I := gridOrder
  have hOrder (i j : I) :
      (∀ e : E, rdeg i e≤ rdeg j e) → @LE.le I gridOrder.toLE i j := coordinate_le
  obtain ⟨v,hv,hRead⟩ := actual_grid_generators D hq hq₂ h0 hπ hMax rdeg hOrder CM L p («F»:=F)
  have hsource (j : IndexType) :
      ∃ h : MvPolynomial H (Jet O k), ∀ f x,
        coeffMod O π P (sourceTop π k d f x h)=
          coeffMod O π P (π^L*evalNormalized D hq hq₂ h0 hπ rdeg (v j f) x) := by
    apply (source_column_iff D hq P k (by omega) hk d hd _).mpr
    intro f
    obtain ⟨w,hw⟩ := hv j f
    refine ⟨w,fun x => ?_⟩
    have hzero : coeffMod O π P
        (rawAt D hq rdeg CM w x-π^L*evalNormalized D hq hq₂ h0 hπ rdeg (v j f) x)=0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_span_singleton.mpr (hw x)
    rw [map_sub,sub_eq_zero] at hzero
    exact hzero
  choose src hs using hsource
  refine ⟨src,fun j => gridColumn D hq hq₂ h0 hπ rdeg (v j),?_,?_⟩
  · intro j i
    apply mod_same L p
    exact hs j i.1 (nodeAt D hq rdeg i.2)
  · intro r fac hfac
    have hz : IsLocalRing.residue O π=0 := by
      apply (IsLocalRing.residue_eq_zero_iff _).mpr
      rw [hMax,Ideal.mem_span_singleton]
    have h := witness_requires_width SR hπ L p hp hz
      (gridReceive D hq hq₂ h0 hπ hMax rdeg CM L p)
      (fun j i => coeffMod O π p (gridColumn D hq hq₂ h0 hπ rdeg (v j) i))
      hRead fac hfac
    simpa using h

#print axioms exact_width_witness
end
end V8CapacityNativeA3

