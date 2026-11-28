import J2R47P9ZeroProbePrinted
import J2R47P9ZeroProbeSideInfo
import J2R43LiteralWholeMenuPublished

/-! This uses the same literal exterior-tied J2 seed and the same
deterministic adaptive bound even with every delivered full-native
zero probe offered for free at its actual address. -/
namespace J2R47P9ZeroProbe
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral
open J6ActiveRun J6R11Blueprint J6R12Blueprint
open Paper5.D1Literal Paper5.HybridClosure J1PhysicalHost J1PPrinted
open J1MainSourceBridge J1MainSourcePlacement J1PhysicalIncidence J1PhysicalCertificate
open J1PhysicalIndependent MainClonedCNF FiniteWeightedQueryTree
open J2R43LiteralWholeMenu V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 11500000
set_option maxRecDepth 2700
set_option Elab.async false
set_option linter.unusedSectionVars false
noncomputable section

variable {B I G : Type} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
variable (M : Match B) (b₀ : B)
variable (special : I) (label : ConfigKey M I→G)
variable (H : Finset (Vertex B)) (f : ℤ[X])
local notation "F" => (edges M)
local notation "reg" => (degree_eq_three M)
local notation "D" => (physicalData M special label)
local notation "Hpin" => (pinSubset M H)
local notation "ZR" => (Box f 1 (sourceQ F f))
local notation "Words" => (Fin (kOf D Hpin)→Bool)
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "A" => (J6ActiveRun.Shape.levelBits (S) 0)

local instance : Nonempty (MainClonedCNF.Port (edges M)) :=
  ⟨.inl (Classical.choice inferInstance,0)⟩

def triangleOr (i : Fin 3) : F :=
  ⟨((b₀,i),next (b₀,i)), Finset.mem_union_left _ ((mem_interior _ _).mpr rfl)⟩

theorem triangle_or_distinct : triangleOr M b₀ 0≠triangleOr M b₀ 1 := by
  intro h
  have h' : (0:Fin 3)=1 := congrArg (fun e : F=>e.val.1.2) h
  exact (by decide : (0:Fin 3)≠1) h'

abbrev ActualZeroQuery (Q : RootPacking F reg f) (d : SourceReady F reg f (fun _=>false)) :=
  J1MainSourceBridge.Menu (PublicSlot F reg f Q d) D Hpin ⊕ DeliveredZeroSlot F reg Q d

def actualAugmentedOracle
    (Q : RootPacking F reg f) (d : SourceReady F reg f (fun _=>false)) (hf : f.Monic)
    (width : ℕ) (node : I→ℚ) (s : Words) (b : Bool) :
    ActualZeroQuery M special label H f Q d → ((ℚ[X]×ZR)⊕FullZeroResponse F reg (f:=f)) :=
  withPublic (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b)
    (actualZeroResponse F reg Q d hf (J1PhysicalNative.actualSigns M b₀ D H s b))

theorem source_J2_adaptive_with_actual_free_zero
    (Q : RootPacking F reg f) (d : SourceReady F reg f (fun _=>false))
    (hf : f.Monic) (hd : 0<f.natDegree)
    (reserve : Reserved F reg Q (triangleOr M b₀ 0) (triangleOr M b₀ 1))
    (erase : ∀ σ : Vertex B→Bool, ∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0)
    (hH : H⊆available M b₀) (hI : Independent M H)
    (width floor : ℕ) (node : I→ℚ)
    (hr : 2≤Fintype.card G) (hR : 32≤width) (hq : 6*width≤Fintype.card I)
    (hHits : ∀ t g,floor≤(hits D Hpin t g).card)
    (tree : DecisionTree (ActualZeroQuery M special label H f Q d)
      ((ℚ[X]×ZR)⊕FullZeroResponse F reg (f:=f)))
    (correct : ∀ s b, evaluate (actualAugmentedOracle M b₀ special label H f Q d hf width node s b) tree
      = decide (0<J1PhysicalNative.actualCount M b₀ D H s b)) :
    ∃ s b,2^kOf D Hpin ≤
      paid (Sum.elim (menuPrice (PublicSlot F reg f Q d) D Hpin floor) (fun _=>0))
        (actualAugmentedOracle M b₀ special label H f Q d hf width node s b) tree := by
  let smaller := eliminatePublic (fixedZeroResponse F reg Q d) tree
  have both (s : Words) (b : Bool) := actual_free_full_zero_exact F reg Q d _ _ reserve hf hd
    (J1PhysicalNative.actualSigns M b₀ D H s b)
    (sameCNFMixedOracle M b₀ special label H f Q d hf width node s b)
    (menuPrice (PublicSlot F reg f Q d) D Hpin floor) tree
  obtain ⟨s,b,pay⟩ := threshold_on_chosen_erased_layout M b₀ special label H f
    Q d hf hH hI width floor node hr hR hq hHits erase smaller
    (fun s b=>(both s b).1.symm.trans (correct s b))
  exact ⟨s,b,(both s b).2.symm ▸ pay⟩

theorem original_exterior_tied_layout_with_full_zero
    (d : SourceReady F reg f (fun _=>false))
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3≤sourceDelta (oldRowSize F))
    (hf : f.Monic) (hd : 0<f.natDegree)
    (size : 1280^2≤oldRowSize F) (i : Fin ((S).levelWidth 0)) :
    ∃ Q : RootPacking F reg f,
      let j : Fin A := Fin.castLE d.widthFits i
      (∀ p : Vertex B,Q.rowLabel (.inr (.inl p)) j=Q.rowLabel (.inr (.inl (M.mate p))) j) ∧
      Fintype.card (DWire F)≤8*2^A*sourceQ F f ∧
      Reserved F reg Q (triangleOr M b₀ 0) (triangleOr M b₀ 1) ∧
      (∀ σ : Vertex B→Bool, ∀ x : PublicSlot F reg f Q d, observedSlot Q d hf σ x=0) ∧
      ∀ (σ : Vertex B→Bool) (x : DeliveredZeroSlot F reg Q d),
        actualZeroResponse F reg Q d hf σ x=fixedZeroResponse F reg Q d x := by
  let j : Fin A := Fin.castLE d.widthFits i
  have hcol : 2*(J9PrintedSchedule.arrayCard A)^2*sourceDelta (oldRowSize F)
      ≤ Nat.card (DWire F) := by
    rw [Nat.card_eq_fintype_card]
    exact d.collision
  have hslots : 2^A*J9PrintedSchedule.arrayCard A≤Nat.card (DWire F) := by
    rw [Nat.card_eq_fintype_card]
    exact d.paddedSlots
  obtain ⟨z,P,htie,_,_⟩ := same_graph_tied_D_seed M j _ hΔ hcol hslots
  obtain ⟨Q,row,_,_,reserve,_,erase,_⟩ := same_printed_J2_layout_full_zero_probes F reg P d
    (triangleOr M b₀ 0) (triangleOr M b₀ 1) (triangle_or_distinct M b₀) hf hd cfg.widthPos size
  have room := actual_printed_reserved_room F reg (f:=f) cfg.widthPos size
  have dpos : (1:ℕ)≤Fintype.card (Cell (Fin A) (Fin 64)) := Fintype.card_pos
  have large : 4*2^A≤Fintype.card (DWire F) := by nlinarith only [room,dpos]
  refine ⟨Q,?_,guardedQ_scale _ _ (by positivity) large,reserve,erase,?_⟩
  · intro p
    rw [row,htie,htie,exterior_pair_tag_equal]
  · intro σ x
    exact congrFun (literal_full_zero_response_is_public F reg Q d _ _ reserve hf hd σ) x

#print axioms triangle_or_distinct
#print axioms source_J2_adaptive_with_actual_free_zero
#print axioms original_exterior_tied_layout_with_full_zero
end
end J2R47P9ZeroProbe

