import V8CapacityNativeA3

/-! The full A4 product is realized by actual integral A1 source
decoders; both inclusion directions use the true active Newton matrix. -/
namespace V8CapacityNativeA4
open scoped Classical BigOperators
open V8CapacitySymbolic V8CapacityJetChart V8CapacityCRTJet
open V8CapacityNativeMatrix V8CapacityNativeCRT V8CapacityIntegrated
open V8CapacityMonicBasis V8CapacityGridOrder V8CapacityNewtonGrid V8CapacitySmith
open V8CapacityWidthGrid V8CapacityNativeA3

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 950000

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
local notation "M" => weighted π q rdeg CM
local notation "SM" => matrixPowered π hMax M
local notation "SR" => (SM).2

def integralMatch (d : κ → O) (v : F → I → O) : Prop :=
  ∃ g : MvPolynomial H (Jet O k), ∀ a x,
    π^P∣sourceTop π k d a x g-π^L*evalNormalized D hq hq₂ h0 hπ rdeg (v a) x

theorem dvd_same_mod (u v : O) (h : π^P∣u-v) :
    coeffMod O π P u=coeffMod O π P v := by
  have z : coeffMod O π P (u-v)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  rwa [map_sub,sub_eq_zero] at z

include hMax in
/-- A normalized column on all fibers is actually attained modulo π^p
iff it belongs to the separately saturated images of true A2. -/
theorem source_saturation (hk : 0<k) (hp : 0<p)
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O)) (v : F → I → O) :
    integralMatch D hq hq₂ h0 hπ L p k d v ↔
      ∀ a : F, realizable π L p (matrixImage M) (v a) := by
  letI : LinearOrder I := gridOrder
  have hOrder (i j : I) :
      (∀ e : E, rdeg i e≤ rdeg j e) → @LE.le I gridOrder.toLE i j := coordinate_le
  let goal (a : F) (x : E → O) : BaseMod O π P :=
    coeffMod O π P (π^L*evalNormalized D hq hq₂ h0 hπ rdeg (v a) x)
  have hm :
      integralMatch D hq hq₂ h0 hπ L p k d v ↔
        ∃ g : MvPolynomial H (Jet O k), ∀ a x,
          coeffMod O π P (sourceTop π k d a x g)=goal a x := by
    constructor
    · rintro ⟨g,hg⟩
      exact ⟨g,fun a x => dvd_same_mod L p _ _ (hg a x)⟩
    · rintro ⟨g,hg⟩
      exact ⟨g,fun a x => mod_same L p _ _ (hg a x)⟩
  rw [hm,source_column_iff D hq P k (by omega) hk d hd goal]
  apply forall_congr'
  intro a
  rw [← exact_readability D hq hq₂ h0 hπ hMax rdeg hOrder CM L p (v a)]
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨w,fun x => mod_same L p _ _ (hw x)⟩
  · rintro ⟨w,hw⟩
    exact ⟨w,fun x => dvd_same_mod L p _ _ (hw x)⟩

/-- Product form exactly over all residues. Factors at d≥L+p are
quotients by π^0 and thus zero. -/
def all_fiber_A4 :
    ((a : F) → (i : Fin (SM).1) → BaseMod O π (p-clipped SR L p i)) ≃ₗ[O]
      (F → observed SR L p) :=
  LinearEquiv.piCongrRight (fun _ => A4_modules SR L p hπ)

/-- The target cyclic product is precisely the family of coordinate
readouts of actually attainable integral source columns. -/
theorem actual_all_fiber_rows (hk : 0<k) (hp : 0<p)
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (z : F → Fin (SM).1 → BaseMod O π p) :
    (∀ a, z a∈observed SR L p) ↔
      ∃ v : F → I → O, integralMatch D hq hq₂ h0 hπ L p k d v ∧
        ∀ a i, coeffMod O π p (coord SR (v a) ((SR).chart.f i))=z a i := by
  simp_rw [source_saturation D hq hq₂ h0 hπ hMax L p k hk hp d hd]
  constructor
  · intro hz
    choose v hv hj using (fun a => (readable_obs SR L p hπ (z a)).mp (hz a))
    exact ⟨v,hv,hj⟩
  · rintro ⟨v,hv,hj⟩ a
    exact (readable_obs SR L p hπ (z a)).mpr ⟨v a,hv a,hj a⟩

#print axioms source_saturation
#print axioms all_fiber_A4
#print axioms actual_all_fiber_rows
end
end V8CapacityNativeA4

