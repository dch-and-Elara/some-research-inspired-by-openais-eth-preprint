
import J2R45BoundedErrorFree
import J2R43LiteralWholeMenuPublished

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 16
set_option maxRecDepth 2500
set_option linter.unusedSectionVars false

/-! Actual MAIN cylinders on the exact J2 mixed oracle. Each D slot
enters with empty support because its same-layout low product is zero. -/
namespace J2R45BoundedError
open scoped Classical Polynomial BigOperators
open Polynomial J6R9Recursive J6R10Integral P11FullPacking J6R10Repack
open J2R43LiteralWholeMenu Paper5.D1Literal Paper5.HybridClosure
open J1PhysicalHost J1PhysicalIndependent J1PhysicalIncidence J1PhysicalCertificate
open J1MainSourceBridge J1MainSourcePlacement MainProbe DiagonalAbundance
open FiniteWeightedQueryTree

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

abbrev SourceQuery (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) :=
  J1MainSourceBridge.Menu (PublicSlot F reg f Q d) D Hpin

def hasMain {C A X : Type*} : C⊕A⊕X→Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr _) => false

def support (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) :
    SourceQuery M special label H f Q d→Finset Words
  | .inl a => pinCylinder Finset.univ a.fixed
  | .inr (.inl (a,g)) =>
    pinCylinder (ownedPins (compiledLayout D Hpin) a.node g Finset.univ) a.fixed
  | .inr (.inr _) => ∅

theorem groups_at_least (floor : ℕ)
    (hitsFloor : ∀ t g,floor≤(hits D Hpin t g).card) :
    ∀ t g,floor≤(ownedPins (compiledLayout D Hpin) t g Finset.univ).card := by
  intro t g
  exact (hitsFloor t g).trans_eq (owned_card_hits D (copies D) (copies_suffice D) Hpin t g).symm

theorem source_support_bound (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (floor : ℕ) (hitsFloor : ∀ t g,floor≤(hits D Hpin t g).card) :
    ∀ q,(support M special label H f Q d q).card≤2^(k-floor) := by
  rintro (a|⟨a,g⟩|x)
  · have h : (support M special label H f Q d (.inl a)).card=1 := by
      simp [support,pinCylinder_card]
    rw [h]
    exact Nat.succ_le_of_lt (pow_pos (by decide) _)
  · change (pinCylinder (ownedPins (compiledLayout D Hpin) a.node g Finset.univ) a.fixed).card≤_
    rw [pinCylinder_card,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left (groups_at_least M special label H floor hitsFloor a.node g) k)
  · simp [support]

theorem source_off_support (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (hf : f.Monic) (width : ℕ) (node : I→ℚ)
    (hr : 2≤Fintype.card G) (hR : 32≤width) (hq : 6*width≤Fintype.card I)
    (erase : ∀ σ : Vertex B→Bool,∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0)
    (s : Words) (b : Bool) (q : SourceQuery M special label H f Q d)
    (hs : s∉support M special label H f Q d q) :
    sameCNFMixedOracle M b₀ special label H f Q d hf width node s b q=0 := by
  rw [sameCNFMixedOracle_eq_zero_simulation M b₀ special label H f Q d hf width node erase]
  have hz : 0∉pubInterval (I:=I) (S:=G) width := zero_not_mem_printedInterval hr hR hq
  rcases q with a|⟨a,g⟩|x
  · change (_, (0:ZR)) = (0,0)
    rw [sourceCompletedProbe_outside_cylinder (compiledLayout D Hpin) _ hz _ node a.node
      Finset.univ a.fibre a.direction a.fixed s (a.other s b) hs]
  · change (_, (0:ZR)) = (0,0)
    rw [sourceGroupProbe_outside_cylinder (compiledLayout D Hpin) _ hz _ node a.node g
      Finset.univ (a.fibre g) a.direction a.fixed s (a.other s b g) hs]
  · simp [zeroSimulated,sourceOracle]

theorem free_D_is_zero (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (hf : f.Monic) (width : ℕ) (node : I→ℚ)
    (erase : ∀ σ : Vertex B→Bool,∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0)
    (s : Words) (b : Bool) (q : SourceQuery M special label H f Q d)
    (hq : hasMain q=false) :
    sameCNFMixedOracle M b₀ special label H f Q d hf width node s b q=0 := by
  rcases q with a|⟨a,g⟩|x
  · cases hq
  · cases hq
  · simp [sameCNFMixedOracle,erase]

theorem enough_words (width floor : ℕ) (hr : 2≤Fintype.card G)
    (hR : 32≤width) (hq : 6*width≤Fintype.card I)
    (hitsFloor : ∀ t g,floor≤(hits D Hpin t g).card) :
    floor≤k := by
  have hI : 0<Fintype.card I := by omega
  have hG : 0<Fintype.card G := by omega
  let t := Classical.choice (Fintype.card_pos_iff.mp hI)
  let g := Classical.choice (Fintype.card_pos_iff.mp hG)
  have h := groups_at_least M special label H floor hitsFloor t g
  have hh := Finset.card_le_univ (ownedPins (compiledLayout D Hpin) t g Finset.univ)
  exact h.trans (by simpa only [Fintype.card_fin] using hh)

theorem actual_count_bit (hH : H⊆available M b₀) (hI : Independent M H)
    (s : Words) (b : Bool) :
    decide (0 < J1PhysicalNative.actualCount M b₀ D H s b)=b := by
  rw [J1PhysicalNative.actualCount_eq M b₀ D H hH hI]
  cases b <;> decide

theorem actual_grouped_bounded_error (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false)) (hf : f.Monic)
    (hH : H⊆available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I→ℚ) (hr : 2≤Fintype.card G) (hR : 32≤width)
    (hq : 6*width≤Fintype.card I) (hitsFloor : ∀ t g,floor≤(hits D Hpin t g).card)
    (erase : ∀ σ : Vertex B→Bool,∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0)
    (seeds : Finset Seed) (hs : seeds.Nonempty) (T : ℕ)
    (trees : Seed→DecisionTree (SourceQuery M special label H f Q d) (ℚ[X]×ZR))
    (bound : ∀ i∈seeds,∀ s b,paid (mainCharge hasMain)
      (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) (trees i)≤T)
    (success : ∀ s b,2*seeds.card≤3*∑ i∈seeds,
      if evaluate (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) (trees i) =
        decide (0 < J1PhysicalNative.actualCount M b₀ D H s b) then 1 else 0) :
    2^floor≤3*T := by
  have hu := finite_seed_bound_with_free_answers (0:ℚ[X]×ZR)
    (sameCNFMixedOracle M b₀ special label H f Q d hf width node)
    (support M special label H f Q d)
    (source_off_support M b₀ special label H f Q d hf width node hr hR hq erase)
    hasMain (free_D_is_zero M b₀ special label H f Q d hf width node erase)
    (2^(k-floor)) (source_support_bound M special label H f Q d floor hitsFloor)
    seeds hs trees Finset.univ T
    (fun i hi s _ b=>bound i hi s b)
    (by
      intro s _ b
      simpa only [actual_count_bit M b₀ special label H hH hI s b] using success s b)
  have hb : (2:ℕ)^k≤3*((2^(k-floor))*T) := by
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hu
  exact remove_capacity_factor k floor T (enough_words M special label H width floor hr hR hq hitsFloor) hb

#print axioms groups_at_least
#print axioms source_support_bound
#print axioms source_off_support
#print axioms free_D_is_zero
#print axioms enough_words
#print axioms actual_grouped_bounded_error
end
end J2R45BoundedError
