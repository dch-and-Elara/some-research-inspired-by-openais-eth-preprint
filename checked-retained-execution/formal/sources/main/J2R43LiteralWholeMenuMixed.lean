
import J2R43LiteralWholeMenuExec
import J1PhysicalNative

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 16
set_option maxRecDepth 2500
set_option linter.unusedSectionVars false

/-! Original J2 on one literal sign family: merge the complete/individual
rational MAIN replies with the completed D reply of the identical four-
clone physical CNF. The D branch is simulated by zero only after the
literal per-address erasure theorem. -/
namespace J2R43LiteralWholeMenu
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral
open Paper5.D1Literal Paper5.HybridClosure J1PPrinted J1PhysicalHost
open J1MainSourceBridge J1MainSourcePlacement J1PhysicalCertificate J1PhysicalIncidence
open FiniteWeightedQueryTree J1PhysicalIndependent MainClonedCNF J6ActiveRun J6R11Blueprint J6R12Blueprint

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

local instance : Nonempty (MainClonedCNF.Port (edges M)) :=
  ⟨.inl (Classical.choice inferInstance,0)⟩

abbrev zeroSimulated
    (P : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (width : ℕ) (node : I→ℚ) (s : Words) (b : Bool) :
    J1MainSourceBridge.Menu (PublicSlot F reg f P d) D Hpin→ℚ[X]×ZR :=
  sourceOracle D Hpin width node (RingHom.id ZR) (fun _ _ _=>(0:ZR[X]))
    (fun _=>0) (fun _=>0) (fun _=>0) s b

def sameCNFMixedOracle
    (P : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (hf : f.Monic) (width : ℕ) (node : I→ℚ) (s : Words) (b : Bool) :
    J1MainSourceBridge.Menu (PublicSlot F reg f P d) D Hpin→ℚ[X]×ZR := fun query=>
  match query with
  | .inr (.inr addr) =>
    (0,observedSlot P d hf (J1PhysicalNative.actualSigns M b₀ D H s b) addr)
  | q => zeroSimulated M special label H f P d width node s b q

theorem sameCNFMixedOracle_eq_zero_simulation
    (P : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (hf : f.Monic) (width : ℕ) (node : I→ℚ)
    (erase : ∀ σ : Vertex B→Bool, ∀ x : PublicSlot F reg f P d, observedSlot P d hf σ x=0)
    (s : Words) (b : Bool) :
    sameCNFMixedOracle M b₀ special label H f P d hf width node s b =
      zeroSimulated M special label H f P d width node s b := by
  funext query
  rcases query with q|q
  · rfl
  · rcases q with q|addr
    · rfl
    · simp [sameCNFMixedOracle,zeroSimulated,sourceOracle,erase]

/-- The raw finite CNF itself, not an independently chosen bit, is the
target of the single adaptive interface. -/
theorem same_physical_count_formula (s : Words) (b : Bool) :
    J1PhysicalNative.actualCount M b₀ D H s b =
      PinnedCNF.modelCount (MainClonedCNF.formula F (leftSlot F reg)
        (rightSlot F reg) (J1PhysicalNative.actualSigns M b₀ D H s b)) := by
  unfold J1PhysicalNative.actualCount
  rw [literal_to_original_formula]

theorem actual_J2_adaptive_threshold
    (seed : RootPacking (edges M) (degree_eq_three M) f)
    (d : SourceReady (edges M) (degree_eq_three M) f (fun _=>false))
    (hf : f.Monic) (hd : 0<f.natDegree)
    (hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 (oldRowSize F))) (size : 320^2≤oldRowSize F)
    (hH : H ⊆ available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I→ℚ)
    (hr : 2≤Fintype.card G) (hR : 32≤width) (hq : 6*width≤Fintype.card I)
    (hHits : ∀ t g,floor≤(hits D Hpin t g).card) :
    ∃ Q : RootPacking F reg f,
      Q.rowLabel=seed.rowLabel ∧ Q.colLabel=seed.colLabel ∧ Q.copies=seed.copies ∧
      Fintype.card (DWire F)≤8*2^((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)*sourceQ F f ∧
      ∀ (tree : DecisionTree (J1MainSourceBridge.Menu (PublicSlot F reg f Q d) D Hpin) (ℚ[X]×ZR)),
        (∀ s b,evaluate (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) tree
          = decide (0 < J1PhysicalNative.actualCount M b₀ D H s b)) →
        ∃ s b,2^kOf D Hpin≤paid (menuPrice (PublicSlot F reg f Q d) D Hpin floor)
          (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b) tree := by
  obtain ⟨Q,hrow,hcol,hcopy,hscale,erase⟩ := whole_printed_menu seed d hf hd hU size
  refine ⟨Q,hrow,hcol,hcopy,hscale,?_⟩
  intro tree correct
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

#print axioms sameCNFMixedOracle_eq_zero_simulation
#print axioms same_physical_count_formula
#print axioms actual_J2_adaptive_threshold
end
end J2R43LiteralWholeMenu
