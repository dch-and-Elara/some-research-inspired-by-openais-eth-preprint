import J2R119ProbabilityBridge
import J2R47ExpectedPublished

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 16
set_option maxRecDepth 2600
set_option linter.unusedSectionVars false

namespace J2R119Probability

open scoped Classical Polynomial BigOperators
open Polynomial J6R9Recursive P11FullPacking J6R10Repack
open J2R43LiteralWholeMenu Paper5.D1Literal Paper5.HybridClosure J1PPrinted
open J1PhysicalHost J1PhysicalIndependent J1PhysicalIncidence J1PhysicalCertificate
open J1MainSourceBridge J1MainSourcePlacement FiniteWeightedQueryTree J2R45BoundedError
open J6ActiveRun J6R11Blueprint J6R12Blueprint

noncomputable section
universe u
variable {B I G : Type} [Fintype B] [DecidableEq B] [Nonempty B]
  [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
variable (M : Match B) (b₀ : B) (special : I) (label : ConfigKey M I → G)
variable (H : Finset (Vertex B)) (f : ℤ[X])
local notation "F" => (edges M)
local notation "reg" => (degree_eq_three M)
local notation "D" => (physicalData M special label)
local notation "Hpin" => (pinSubset M H)
local notation "k" => (kOf D Hpin)
local notation "ZR" => (Box f 1 (sourceQ F f))
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local instance : Nonempty (MainClonedCNF.Port (edges M)) := ⟨.inl (Classical.choice inferInstance,0)⟩

def GroupedProbabilityGuarantee (Q : RootPacking F reg f)
    (d : SourceReady F reg f (fun _ => false)) (hf : f.Monic)
    (width floor : ℕ) (node : I → ℚ) : Prop :=
  ExpectedGuarantee.{u}
    (sameCNFMixedOracle M b₀ special label H f Q d hf width node) hasMain
    (fun s b => decide (0 < J1PhysicalNative.actualCount M b₀ D H s b)) floor

def CompleteOnlyProbabilityGuarantee (Q : RootPacking F reg f)
    (d : SourceReady F reg f (fun _ => false)) (hf : f.Monic)
    (width : ℕ) (node : I → ℚ) : Prop :=
  ExpectedGuarantee.{u}
    (completeOnlyOracle M b₀ special label H f Q d hf width node) countsCompleteOnly
    (fun s b => decide (0 < J1PhysicalNative.actualCount M b₀ D H s b)) k

theorem actual_grouped_probability (Q : RootPacking F reg f)
    (d : SourceReady F reg f (fun _ => false)) (hf : f.Monic)
    (hH : H ⊆ available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I → ℚ) (hr : 2 ≤ Fintype.card G)
    (hR : 32 ≤ width) (hq : 6*width ≤ Fintype.card I)
    (hitsFloor : ∀ t g, floor ≤ (hits D Hpin t g).card)
    (erase : ∀ σ : Vertex B → Bool, ∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x = 0) :
    GroupedProbabilityGuarantee.{u} M b₀ special label H f Q d hf width floor node := by
  exact words_expected (enough_words M special label H width floor hr hR hq hitsFloor)
    (0 : ℚ[X] × ZR) _ hasMain _
    (actual_count_bit M b₀ special label H hH hI)
    (support M special label H f Q d)
    (source_off_support M b₀ special label H f Q d hf width node hr hR hq erase)
    (free_D_is_zero M b₀ special label H f Q d hf width node erase)
    (source_support_bound M special label H f Q d floor hitsFloor)

theorem actual_complete_only_probability (Q : RootPacking F reg f)
    (d : SourceReady F reg f (fun _ => false)) (hf : f.Monic)
    (hH : H ⊆ available M b₀) (hI : Independent M H)
    (width : ℕ) (node : I → ℚ) (hr : 2 ≤ Fintype.card G)
    (hR : 32 ≤ width) (hq : 6*width ≤ Fintype.card I)
    (erase : ∀ σ : Vertex B → Bool, ∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x = 0) :
    CompleteOnlyProbabilityGuarantee.{u} M b₀ special label H f Q d hf width node := by
  let lift := insertCompleteOnly M special label H f Q d
  have hOff := source_off_support M b₀ special label H f Q d hf width node hr hR hq erase
  have hfree : ∀ s b (q : CompleteOnlyQuery M special label H f Q d), countsCompleteOnly q = false →
      completeOnlyOracle M b₀ special label H f Q d hf width node s b q = 0 := by
    intro s b q hq'
    rcases q with a | x
    · cases hq'
    · exact free_D_is_zero M b₀ special label H f Q d hf width node erase s b
        (Sum.inr (Sum.inr x)) rfl
  unfold CompleteOnlyProbabilityGuarantee ExpectedGuarantee
  intro Seed seedSpace μ seedLaw budget trees measCost measSuccess mean success
  exact @complete_words_expected _ _ k (0 : ℚ[X] × ZR)
    (completeOnlyOracle M b₀ special label H f Q d hf width node) countsCompleteOnly
    (fun s b => decide (0 < J1PhysicalNative.actualCount M b₀ D H s b))
    (actual_count_bit M b₀ special label H hH hI)
    (fun q => support M special label H f Q d (lift q))
    (fun s b q h => hOff s b (lift q) h) hfree
    (complete_only_support_bound M special label H f Q d)
    Seed seedSpace μ seedLaw budget trees measCost measSuccess mean success

/-- One original layout, including the actual public replies and erasure,
supports both paid-query statements for arbitrary probability spaces. -/
theorem actual_J2_published_expected_probability
    (d : SourceReady F reg f (fun _ => false))
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3 ≤ sourceDelta (oldRowSize F))
    (hf : f.Monic) (hd : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (size : 320^2 ≤ oldRowSize F)
    (i : Fin ((S).levelWidth 0))
    (hH : H ⊆ available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I → ℚ) (hr : 2 ≤ Fintype.card G)
    (hR : 32 ≤ width) (hq : 6*width ≤ Fintype.card I)
    (hitsFloor : ∀ t g, floor ≤ (hits D Hpin t g).card) :
    ∃ Q : RootPacking F reg f,
      let j : Fin ((S).levelBits 0) := Fin.castLE d.widthFits i
      (∀ p : Vertex B, Q.rowLabel (.inr (.inl p)) j = Q.rowLabel (.inr (.inl (M.mate p))) j) ∧
      Fintype.card (DWire F) ≤ 8*2^((S).levelBits 0)*sourceQ F f ∧
      (∀ σ : Vertex B → Bool, ∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x = 0) ∧
      (∀ (σ : Vertex B → Bool) (x : PublicAddress F reg f Q d),
        IsActualHighReply Q d hf σ (getReady cfg (oldRowRoot_stable F reg f σ hΔ) d.active)
          x (publicReply F reg f Q d hf σ x)) ∧
      GroupedGuarantee.{u} M b₀ special label H f Q d hf width floor node ∧
      CompleteOnlyGuarantee.{u} M b₀ special label H f Q d hf width node ∧
      GroupedProbabilityGuarantee.{u} M b₀ special label H f Q d hf width floor node ∧
      CompleteOnlyProbabilityGuarantee.{u} M b₀ special label H f Q d hf width node := by
  obtain ⟨Q, ht, hscale, herase, hactual, hg, hc⟩ :=
    actual_J2_both_bounded_error_thresholds.{u} M b₀ special label H f
      d cfg hΔ hf hd size i hH hI width floor node hr hR hq hitsFloor
  exact ⟨Q, ht, hscale, herase, hactual, hg, hc,
    actual_grouped_probability M b₀ special label H f Q d hf hH hI
      width floor node hr hR hq hitsFloor herase,
    actual_complete_only_probability M b₀ special label H f Q d hf hH hI
      width node hr hR hq herase⟩

#print axioms GroupedProbabilityGuarantee
#print axioms CompleteOnlyProbabilityGuarantee
#print axioms actual_grouped_probability
#print axioms actual_complete_only_probability
#print axioms actual_J2_published_expected_probability

end
end J2R119Probability

