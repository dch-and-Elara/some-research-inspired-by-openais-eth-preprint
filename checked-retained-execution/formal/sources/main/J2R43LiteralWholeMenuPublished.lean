
import J2R43LiteralWholeMenuMixed
import J2R43LiteralWholeMenuSeed

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 16
set_option maxRecDepth 2500
set_option linter.unusedSectionVars false

/-! The selected seed, P9 reseating, exact mode reply, and adaptive
threshold all refer to a single actual four-clone root on edges M. -/
namespace J2R43LiteralWholeMenu
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral
open J6ActiveRun J6R11Blueprint J6R12Blueprint
open Paper5.D1Literal Paper5.HybridClosure J1PhysicalHost J1PPrinted
open J1MainSourceBridge J1MainSourcePlacement J1PhysicalIncidence J1PhysicalCertificate
open J1PhysicalIndependent MainClonedCNF FiniteWeightedQueryTree

noncomputable section
variable {B I G : Type} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
variable (M : Match B) (b₀ : B) (special : I) (label : ConfigKey M I→G)
variable (H : Finset (Vertex B))
variable (f : ℤ[X])
local notation "F" => (edges M)
local notation "reg" => (degree_eq_three M)
local notation "D" => (physicalData M special label)
local notation "Hpin" => (pinSubset M H)
local notation "ZR" => (Box f 1 (sourceQ F f))
local notation "Words" => (Fin (kOf D Hpin)→Bool)
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))

local instance : Nonempty (MainClonedCNF.Port (edges M)) :=
  ⟨.inl (Classical.choice inferInstance,0)⟩

theorem threshold_on_chosen_erased_layout
    (Q : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (hf : f.Monic)
    (hH : H ⊆ available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I→ℚ)
    (hr : 2≤Fintype.card G) (hR : 32≤width) (hq : 6*width≤Fintype.card I)
    (hHits : ∀ t g,floor≤(hits D Hpin t g).card)
    (erase : ∀ σ : Vertex B→Bool, ∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0)
    (tree : DecisionTree (J1MainSourceBridge.Menu (PublicSlot F reg f Q d) D Hpin) (ℚ[X]×ZR))
    (correct : ∀ s b,evaluate (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) tree
      = decide (0 < J1PhysicalNative.actualCount M b₀ D H s b)) :
    ∃ s b,2^kOf D Hpin≤paid (menuPrice (PublicSlot F reg f Q d) D Hpin floor)
      (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) tree := by
  have eq (s : Words) (b : Bool) := sameCNFMixedOracle_eq_zero_simulation M b₀ special label H f
    Q d hf width node erase s b
  obtain ⟨s,b,pay⟩ := J1PhysicalNative.native_path_on_physical_count
    (R:=ZR) (O:=ZR) («D»:=PublicSlot F reg f Q d) M b₀ special label H hH hI
    width floor node hr hR hq hHits (RingHom.id ZR) (sourceQ F f)
    (box_two_nil (sourceQ F f) f 1) (fun _ _ _=>0) (fun _=>0) (fun _=>0) (fun _=>0)
    (fun _=>le_rfl) (fun _ _ _ _=>by simp) tree (by
      intro s b
      have h := correct s b
      rw [eq s b] at h
      exact h)
  refine ⟨s,b,?_⟩
  rw [eq s b]
  exact pay

theorem actual_J2_on_original_exterior_tied_layout
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3≤sourceDelta (oldRowSize F))
    (hf : f.Monic) (hd : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (size : 320^2≤oldRowSize F)
    (i : Fin ((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelWidth 0))
    (hH : H ⊆ available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I→ℚ)
    (hr : 2≤Fintype.card G) (hR : 32≤width) (hq : 6*width≤Fintype.card I)
    (hHits : ∀ t g,floor≤(hits D Hpin t g).card) :
    ∃ Q : RootPacking F reg f,
      let j : Fin ((S).levelBits 0) := Fin.castLE d.widthFits i
      (∀ p : Vertex B,Q.rowLabel (.inr (.inl p)) j=Q.rowLabel (.inr (.inl (M.mate p))) j) ∧
      Fintype.card (DWire F)≤8*2^((S).levelBits 0)*sourceQ F f ∧
      (∀ σ : Vertex B→Bool, ∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0) ∧
      (∀ (σ : Vertex B→Bool) (x : PublicAddress F reg f Q d),
        IsActualHighReply Q d hf σ (getReady cfg (oldRowRoot_stable F reg f σ hΔ) d.active)
          x (publicReply F reg f Q d hf σ x)) ∧
      ∀ (tree : DecisionTree (J1MainSourceBridge.Menu (PublicSlot F reg f Q d) D Hpin) (ℚ[X]×ZR)),
        (∀ s b,evaluate (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) tree
          = decide (0 < J1PhysicalNative.actualCount M b₀ D H s b)) →
        ∃ s b,2^kOf D Hpin≤paid (menuPrice (PublicSlot F reg f Q d) D Hpin floor)
          (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) tree := by
  let j : Fin ((S).levelBits 0) := Fin.castLE d.widthFits i
  have hcol : 2*(J9PrintedSchedule.arrayCard ((S).levelBits 0))^2*sourceDelta (oldRowSize F)
      ≤ Nat.card (DWire F) := by
    rw [Nat.card_eq_fintype_card]
    exact d.collision
  have hslots : 2^((S).levelBits 0)*J9PrintedSchedule.arrayCard ((S).levelBits 0)≤Nat.card (DWire F) := by
    rw [Nat.card_eq_fintype_card]
    exact d.paddedSlots
  obtain ⟨z,P,htie,_,_⟩ := same_graph_tied_D_seed M j _ hΔ hcol hslots
  obtain ⟨Q,hrw,_,_,hscale,herase⟩ := whole_printed_menu P d hf hd cfg.widthPos size
  refine ⟨Q,?_,hscale,herase,?_,?_⟩
  · intro p
    rw [hrw,htie,htie,exterior_pair_tag_equal]
  · intro σ x
    exact public_reply_is_actual Q d cfg hΔ hf hd σ _ x
  · exact threshold_on_chosen_erased_layout M b₀ special label H f Q d hf hH hI
      width floor node hr hR hq hHits herase

#print axioms threshold_on_chosen_erased_layout
#print axioms actual_J2_on_original_exterior_tied_layout
end
end J2R43LiteralWholeMenu
