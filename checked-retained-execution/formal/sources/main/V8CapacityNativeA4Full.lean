import V8CapacityNativeA4

/-! Options not assumed in the A4 direction: normalize an arbitrary
source decoder whose divided output is integral on the whole domain;
prove that finite grid receipts determine all such output functions. -/
namespace V8CapacityNativeA4
open scoped Classical BigOperators
open V8CapacitySymbolic V8CapacityJetChart V8CapacityCRTJet
open V8CapacityNativeMatrix V8CapacityNativeCRT V8CapacityIntegrated
open V8CapacityMonicBasis V8CapacityGridOrder V8CapacityNewtonGrid V8CapacitySmith
open V8CapacityNativeA3

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 950000

variable {O H : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [IsPrincipalIdealRing O] [Fintype H]
variable [Fintype (IsLocalRing.ResidueField O)]
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

include hMax in
theorem every_integral_source_normalizes (hk : 0<k) (hp : 0<p)
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (g : MvPolynomial H (Jet O k)) (hi : ∀ a x, π^L∣sourceTop π k d a x g) :
    ∃ v : F → I → O, ∀ a x,
      π^P∣sourceTop π k d a x g-π^L*evalNormalized D hq hq₂ h0 hπ rdeg (v a) x := by
  letI : LinearOrder I := gridOrder
  have hOrder (i j : I) :
      (∀ e : E, rdeg i e≤ rdeg j e) → @LE.le I gridOrder.toLE i j := coordinate_le
  have hk' : ∀ a : F, ∃ w : C → O, ∀ x : E → O,
      coeffMod O π P (rawAt D hq rdeg CM w x)=coeffMod O π P (sourceTop π k d a x g) :=
    (source_column_iff D hq P k (by omega) hk d hd _).mp ⟨g,fun _ _ => rfl⟩
  choose w hw using hk'
  have hraw (a : F) (x : E → O) : π^P∣sourceTop π k d a x g-rawAt D hq rdeg CM (w a) x :=
    mod_same L p _ _ (hw a x).symm
  have hdvd (a : F) (x : E → O) : π^L∣rawAt D hq rdeg CM (w a) x := by
    have hr := (pow_dvd_pow π (show L≤P by omega)).trans (hraw a x)
    convert dvd_sub (hi a x) hr using 1
    ring
  have hcoeff (a : F) := all_readable_output_integral_coefficients D hq hq₂ h0 hπ hMax rdeg
    hOrder CM (w a) L (hdvd a)
  choose v hv using hcoeff
  refine ⟨v,fun a x => ?_⟩
  have hmod : rawAt D hq rdeg CM (w a) x =
      π^L * evalNormalized D hq hq₂ h0 hπ rdeg (v a) x := by
    rw [rawAt_normalized D hq hq₂ h0 hπ]
    unfold evalNormalized
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hv a i]
    ring
  rw [← hmod]
  exact hraw a x

#print axioms every_integral_source_normalizes
end
end V8CapacityNativeA4