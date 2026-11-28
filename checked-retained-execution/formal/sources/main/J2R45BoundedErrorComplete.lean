
import J2R45BoundedErrorNative

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 16
set_option maxRecDepth 2100
set_option linter.unusedSectionVars false

/-! The original sharper bounded-error threshold when only completed MAIN
jets and freely supplied D completed residues are exposed. -/
namespace J2R45BoundedError
open scoped Polynomial Classical BigOperators
open Polynomial J6R9Recursive P11FullPacking J6R10Repack
open J2R43LiteralWholeMenu Paper5.D1Literal Paper5.HybridClosure
open J1PhysicalHost J1PhysicalIndependent J1PhysicalIncidence J1PhysicalCertificate
open J1MainSourceBridge J1MainSourcePlacement MainProbe DiagonalAbundance FiniteWeightedQueryTree

noncomputable section
variable {B I G : Type} [Fintype B] [DecidableEq B] [Nonempty B]
  [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
variable {Seed : Type*}
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

abbrev CompleteOnlyQuery (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) :=
  NativeJ2.Address I G (J1PhysicalIncidence.Variable (Vertex B)) k ⊕ PublicSlot F reg f Q d

def insertCompleteOnly (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) :
    CompleteOnlyQuery M special label H f Q d→SourceQuery M special label H f Q d
  | .inl a => .inl a
  | .inr x => .inr (.inr x)

def countsCompleteOnly {A X : Type*} : A⊕X→Bool
  | .inl _=>true
  | .inr _=>false

abbrev completeOnlyOracle (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (hf : f.Monic) (width : ℕ) (node : I→ℚ) (s : Words) (b : Bool) :
    CompleteOnlyQuery M special label H f Q d→ℚ[X]×ZR :=
  sameCNFMixedOracle M b₀ special label H f Q d hf width node s b ∘
    insertCompleteOnly M special label H f Q d

theorem complete_only_support_bound (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) :
    ∀ q,(support M special label H f Q d (insertCompleteOnly M special label H f Q d q)).card≤1 := by
  rintro (a|x)
  · simp [insertCompleteOnly,support,pinCylinder_card]
  · simp [insertCompleteOnly,support]

theorem actual_complete_only_bounded_error (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) (hf : f.Monic)
    (hH : H⊆available M b₀) (hI : Independent M H)
    (width : ℕ) (node : I→ℚ) (hr : 2≤Fintype.card G) (hR : 32≤width) (hq : 6*width≤Fintype.card I)
    (erase : ∀ σ : Vertex B→Bool,∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0)
    (seeds : Finset Seed) (hs : seeds.Nonempty) (T : ℕ)
    (trees : Seed→DecisionTree (CompleteOnlyQuery M special label H f Q d) (ℚ[X]×ZR))
    (bound : ∀ i∈seeds,∀ s b,paid (mainCharge countsCompleteOnly)
      (completeOnlyOracle M b₀ special label H f Q d hf width node s b) (trees i)≤T)
    (success : ∀ s b,2*seeds.card≤3*∑ i∈seeds,
      if evaluate (completeOnlyOracle M b₀ special label H f Q d hf width node s b) (trees i) =
        decide (0 < J1PhysicalNative.actualCount M b₀ D H s b) then 1 else 0) :
    2^k≤3*T := by
  let lift := insertCompleteOnly M special label H f Q d
  have hOff := source_off_support M b₀ special label H f Q d hf width node hr hR hq erase
  have hfree : ∀ s b (q : CompleteOnlyQuery M special label H f Q d), countsCompleteOnly q=false →
      completeOnlyOracle M b₀ special label H f Q d hf width node s b q=0 := by
    intro s b q hq'
    rcases q with a|x
    · cases hq'
    · exact free_D_is_zero M b₀ special label H f Q d hf width node erase s b
        (Sum.inr (Sum.inr x)) rfl
  have hu := finite_seed_bound_with_free_answers (0:ℚ[X]×ZR)
    (completeOnlyOracle M b₀ special label H f Q d hf width node)
    (fun q=>support M special label H f Q d (lift q))
    (fun s b q hs'=>hOff s b (lift q) hs')
    countsCompleteOnly hfree 1 (complete_only_support_bound M special label H f Q d)
    seeds hs trees Finset.univ T
    (fun i hi s _ b=>bound i hi s b)
    (by
      intro s _ b
      simpa only [actual_count_bit M b₀ special label H hH hI s b] using success s b)
  simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,one_mul] using hu

#print axioms complete_only_support_bound
#print axioms actual_complete_only_bounded_error
end
end J2R45BoundedError
