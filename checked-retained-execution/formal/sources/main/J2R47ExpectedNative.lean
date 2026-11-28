import J2R47ExpectedMarkov
import J2R45BoundedErrorComplete

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 16
set_option maxRecDepth 2600
set_option linter.unusedSectionVars false

/-! The two original J2 physical menus. A uniform worst-case bound on
the sum of the R45 paid MAIN query counts over the finite seed set,
not a per-seed hard limit, suffices. -/
namespace J2R47Expected
open scoped Classical Polynomial BigOperators
open Polynomial J6R9Recursive J6R10Integral P11FullPacking J6R10Repack
open J2R43LiteralWholeMenu Paper5.D1Literal Paper5.HybridClosure
open J1PhysicalHost J1PhysicalIndependent J1PhysicalIncidence J1PhysicalCertificate
open J1MainSourceBridge J1MainSourcePlacement FiniteWeightedQueryTree J2R45BoundedError

noncomputable section
universe u
variable {B I G : Type} [Fintype B] [DecidableEq B] [Nonempty B]
  [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
variable {Seed : Type u}
variable (M : Match B) (b₀ : B) (special : I) (label : ConfigKey M I→G)
variable (H : Finset (Vertex B)) (f : ℤ[X])
local notation "F" => (edges M)
local notation "reg" => (degree_eq_three M)
local notation "D" => (physicalData M special label)
local notation "Hpin" => (pinSubset M H)
local notation "ZR" => (Box f 1 (sourceQ F f))
local notation "k" => (kOf D Hpin)
local notation "Words" => (Fin k→Bool)
local instance : Nonempty (MainClonedCNF.Port (edges M)) := ⟨.inl (Classical.choice inferInstance,0)⟩

theorem actual_grouped_expected (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) (hf : f.Monic)
    (hH : H⊆available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I→ℚ) (hr : 2≤Fintype.card G) (hR : 32≤width)
    (hq : 6*width≤Fintype.card I) (hitsFloor : ∀ t g,floor≤(hits D Hpin t g).card)
    (erase : ∀ σ : Vertex B→Bool,∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0)
    (seeds : Finset Seed) (hs : seeds.Nonempty) (total : ℕ)
    (trees : Seed→DecisionTree (SourceQuery M special label H f Q d) (ℚ[X]×ZR))
    (budget : ∀ s b,(∑ i∈seeds,paid (mainCharge hasMain)
      (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) (trees i))≤total)
    (success : ∀ s b,2*seeds.card≤3*∑ i∈seeds,
      if evaluate (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) (trees i)=
        decide (0 < J1PhysicalNative.actualCount M b₀ D H s b) then 1 else 0) :
    2^floor*seeds.card≤72*total := by
  let T := (12*total)/seeds.card
  have hu := capacity_at_cutoff (0:ℚ[X]×ZR)
    (sameCNFMixedOracle M b₀ special label H f Q d hf width node)
    (support M special label H f Q d)
    (source_off_support M b₀ special label H f Q d hf width node hr hR hq erase)
    hasMain (free_D_is_zero M b₀ special label H f Q d hf width node erase)
    (2^(k-floor)) T (source_support_bound M special label H f Q d floor hitsFloor)
    seeds hs trees Finset.univ
    (fun s _ b=>(Nat.mul_le_mul_left 12 (budget s b)).trans
      (mean_to_cutoff seeds.card total (Finset.card_pos.mpr hs)))
    (by
      intro s _ b
      simpa only [actual_count_bit M b₀ special label H hH hI s b] using success s b)
  have hb : (2:ℕ)^k≤6*((2^(k-floor))*T) := by
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hu
  have hp : (2:ℕ)^k≤3*((2^(k-floor))*(2*T)) := calc
    _ ≤ 6*((2^(k-floor))*T) := hb
    _ = _ := by ring
  have hx := remove_capacity_factor k floor (2*T) (enough_words M special label H width floor hr hR hq hitsFloor) hp
  have h6 : (2:ℕ)^floor≤6*T := by omega
  exact mean_bound_from_cutoff seeds.card total _ h6

theorem actual_complete_only_expected (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) (hf : f.Monic)
    (hH : H⊆available M b₀) (hI : Independent M H)
    (width : ℕ) (node : I→ℚ) (hr : 2≤Fintype.card G) (hR : 32≤width)
    (hq : 6*width≤Fintype.card I)
    (erase : ∀ σ : Vertex B→Bool,∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0)
    (seeds : Finset Seed) (hs : seeds.Nonempty) (total : ℕ)
    (trees : Seed→DecisionTree (CompleteOnlyQuery M special label H f Q d) (ℚ[X]×ZR))
    (budget : ∀ s b,(∑ i∈seeds,paid (mainCharge countsCompleteOnly)
      (completeOnlyOracle M b₀ special label H f Q d hf width node s b) (trees i))≤total)
    (success : ∀ s b,2*seeds.card≤3*∑ i∈seeds,
      if evaluate (completeOnlyOracle M b₀ special label H f Q d hf width node s b) (trees i)=
        decide (0 < J1PhysicalNative.actualCount M b₀ D H s b) then 1 else 0) :
    2^k*seeds.card≤72*total := by
  let T := (12*total)/seeds.card
  let lift := insertCompleteOnly M special label H f Q d
  have hOff := source_off_support M b₀ special label H f Q d hf width node hr hR hq erase
  have hfree : ∀ s b (q : CompleteOnlyQuery M special label H f Q d), countsCompleteOnly q=false →
      completeOnlyOracle M b₀ special label H f Q d hf width node s b q=0 := by
    intro s b q hq'
    rcases q with a|x
    · cases hq'
    · exact free_D_is_zero M b₀ special label H f Q d hf width node erase s b
        (Sum.inr (Sum.inr x)) rfl
  have hu := capacity_at_cutoff (0:ℚ[X]×ZR)
    (completeOnlyOracle M b₀ special label H f Q d hf width node)
    (fun q=>support M special label H f Q d (lift q))
    (fun s b q hs'=>hOff s b (lift q) hs')
    countsCompleteOnly hfree 1 T (complete_only_support_bound M special label H f Q d)
    seeds hs trees Finset.univ
    (fun s _ b=>(Nat.mul_le_mul_left 12 (budget s b)).trans
      (mean_to_cutoff seeds.card total (Finset.card_pos.mpr hs)))
    (by
      intro s _ b
      simpa only [actual_count_bit M b₀ special label H hH hI s b] using success s b)
  have h6 : (2:ℕ)^k≤6*T := by
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,one_mul] using hu
  exact mean_bound_from_cutoff seeds.card total _ h6

#print axioms actual_grouped_expected
#print axioms actual_complete_only_expected
end
end J2R47Expected
