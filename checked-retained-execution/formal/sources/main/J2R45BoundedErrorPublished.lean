
import J2R45BoundedErrorComplete

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 16
set_option maxRecDepth 2400
set_option linter.unusedSectionVars false

/-! Both original randomized thresholds on the identical actual layout
already carrying deterministic J2. No additional group-read interface
or bound on high-precision D acquisition is assumed. -/
namespace J2R45BoundedError
open scoped Classical Polynomial BigOperators
open Polynomial J6R9Recursive P11FullPacking J6R10Repack
open J2R43LiteralWholeMenu Paper5.D1Literal Paper5.HybridClosure J1PPrinted
open J1PhysicalHost J1PhysicalIndependent J1PhysicalIncidence J1PhysicalCertificate
open J1MainSourceBridge J1MainSourcePlacement FiniteWeightedQueryTree
open J6ActiveRun J6R11Blueprint J6R12Blueprint

noncomputable section
universe u
variable {B I G : Type} [Fintype B] [DecidableEq B] [Nonempty B]
  [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
variable (M : Match B) (b₀ : B) (special : I) (label : ConfigKey M I→G)
variable (H : Finset (Vertex B)) (f : ℤ[X])
local notation "F" => (edges M)
local notation "reg" => (degree_eq_three M)
local notation "D" => (physicalData M special label)
local notation "Hpin" => (pinSubset M H)
local notation "ZR" => (Box f 1 (sourceQ F f))
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local instance : Nonempty (MainClonedCNF.Port (edges M)) := ⟨.inl (Classical.choice inferInstance,0)⟩

def GroupedGuarantee (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) (hf : f.Monic)
    (width floor : ℕ) (node : I→ℚ) : Prop :=
  ∀ {Seed : Type u} (seeds : Finset Seed) (_ : seeds.Nonempty) (T : ℕ)
    (trees : Seed→DecisionTree (SourceQuery M special label H f Q d) (ℚ[X]×ZR)),
    (∀ i∈seeds,∀ s b,paid (mainCharge hasMain)
      (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) (trees i)≤T) →
    (∀ s b,2*seeds.card≤3*∑ i∈seeds,
      if evaluate (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) (trees i) =
        decide (0 < J1PhysicalNative.actualCount M b₀ D H s b) then 1 else 0) →
    2^floor≤3*T

def CompleteOnlyGuarantee (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) (hf : f.Monic)
    (width : ℕ) (node : I→ℚ) : Prop :=
  ∀ {Seed : Type u} (seeds : Finset Seed) (_ : seeds.Nonempty) (T : ℕ)
    (trees : Seed→DecisionTree (CompleteOnlyQuery M special label H f Q d) (ℚ[X]×ZR)),
    (∀ i∈seeds,∀ s b,paid (mainCharge countsCompleteOnly)
      (completeOnlyOracle M b₀ special label H f Q d hf width node s b) (trees i)≤T) →
    (∀ s b,2*seeds.card≤3*∑ i∈seeds,
      if evaluate (completeOnlyOracle M b₀ special label H f Q d hf width node s b) (trees i) =
        decide (0 < J1PhysicalNative.actualCount M b₀ D H s b) then 1 else 0) →
    2^kOf D Hpin≤3*T

theorem actual_J2_both_bounded_error_thresholds
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3≤sourceDelta (oldRowSize F))
    (hf : f.Monic) (hd : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (size : 320^2≤oldRowSize F)
    (i : Fin ((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelWidth 0))
    (hH : H⊆available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I→ℚ) (hr : 2≤Fintype.card G)
    (hR : 32≤width) (hq : 6*width≤Fintype.card I)
    (hitsFloor : ∀ t g,floor≤(hits D Hpin t g).card) :
    ∃ Q : RootPacking F reg f,
      let j : Fin ((S).levelBits 0) := Fin.castLE d.widthFits i
      (∀ p : Vertex B,Q.rowLabel (.inr (.inl p)) j=Q.rowLabel (.inr (.inl (M.mate p))) j) ∧
      Fintype.card (DWire F)≤8*2^((S).levelBits 0)*sourceQ F f ∧
      (∀ σ : Vertex B→Bool, ∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0) ∧
      (∀ (σ : Vertex B→Bool) (x : PublicAddress F reg f Q d),
        IsActualHighReply Q d hf σ (getReady cfg (oldRowRoot_stable F reg f σ hΔ) d.active)
          x (publicReply F reg f Q d hf σ x)) ∧
      GroupedGuarantee.{u} M b₀ special label H f Q d hf width floor node ∧
      CompleteOnlyGuarantee.{u} M b₀ special label H f Q d hf width node := by
  obtain ⟨Q,ht,hqScale,herase,hactual,_⟩ := actual_J2_on_original_exterior_tied_layout M b₀ special label H f
    d cfg hΔ hf hd size i hH hI width floor node hr hR hq hitsFloor
  refine ⟨Q,ht,hqScale,herase,hactual,?_,?_⟩
  · intro Seed seeds hs T trees bound success
    exact actual_grouped_bounded_error M b₀ special label H f Q d hf hH hI
      width floor node hr hR hq hitsFloor herase seeds hs T trees bound success
  · intro Seed seeds hs T trees bound success
    exact actual_complete_only_bounded_error M b₀ special label H f Q d hf hH hI
      width node hr hR hq herase seeds hs T trees bound success

#print axioms GroupedGuarantee
#print axioms CompleteOnlyGuarantee
#print axioms actual_J2_both_bounded_error_thresholds
end
end J2R45BoundedError
