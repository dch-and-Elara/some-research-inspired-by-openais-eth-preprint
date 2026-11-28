import V8NativeMessageN7LiteralSupportKill
import V8NativeMessageN7LiteralSupportOrientation
import V8NativeMessageN7LiteralSupportZero

/-! A genuine source unary pin is a distinct physical row wire. The
negative zero statement needs no assumptions about cancellation. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9PacketTiles
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R9Recursive
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000
set_option maxRecDepth 2300
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)
local notation "E" => (DWire F)

omit [Fintype W] [DecidableEq W] in
def sourceUnaryWire : W ↪ E :=
  ⟨fun v=>(.inl v,true),fun _ _ h=>Sum.inl.inj (congrArg Prod.fst h)⟩

theorem actual_positive_unary_source_zero {R : Type} [CommRing R] {a : ℕ}
    (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) (v : W)
    (positive : σ v=true)
    (absent : ¬ ∃ q : E,Matches P t (sourceUnaryWire F v) q) :
    flatSigned P t κ (oldRowTruth F reg σ)=0 :=
  missing_required_inputs_kills_flat P t κ (oldRowTruth F reg σ)
    (.inl (.inr (.inl v))) {sourceUnaryWire F v}
    (fun _ hr q h=>absent ⟨q,(Finset.mem_singleton.mp hr) ▸ h⟩)
    (fun w zeroOn=>by
      have h := zeroOn (sourceUnaryWire F v) (Finset.mem_singleton_self _)
      change decide (w (.inl (sourceUnaryWire F v))=σ v)=false
      rw [positive,h]
      decide)

variable {f : ℤ[X]} (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

theorem original_all_true_nonzero_requires_every_pin
    (hf : f.Monic) (hd : 0<f.natDegree) (x : PublicSlot F reg f P d)
    (zeroProbe : siteProbe F reg d x.1 x.2.1=0)
    (nonzero : wholePublic F reg P d hf (fun _=>true) x≠0) :
    ∀ v : W,∃ q,Matches P x.1.val (sourceUnaryWire F v) q := by
  intro v
  by_contra absent
  apply nonzero
  rw [original_public_full_zero_probe F reg P d hf hd _ x zeroProbe]
  split
  · rw [exactZero,full_signed_root_is_zero_polynomial,full_root_at_zero_has_literal_two_cubes P
      (PublicIndex F reg f d x.1) (centerNonzero x.1) rfl,
      actual_positive_unary_source_zero F reg P _ _ (fun _=>true) v rfl absent,map_zero]
  · rfl

theorem actual_geometric_capacity_excludes_original_slot
    (hf : f.Monic) (hd : 0<f.natDegree) (x : PublicSlot F reg f P d)
    (zeroProbe : siteProbe F reg d x.1 x.2.1=0)
    (tooFew : (3*Fintype.card (DWire F)/2^((printedParams (f:=f) (ell:=1)
        (oldRowSize F)).levelBits 0)) *
      (2^((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)-x.1.val.natAbs)
      <Fintype.card W) :
    wholePublic F reg P d hf (fun _=>true) x=0 := by
  by_contra nonzero
  exact (not_le_of_gt tooFew) (all_required_rows_force_matched_capacity P (sourceUnaryWire F) x.1.val
    (original_all_true_nonzero_requires_every_pin F reg P d hf hd x zeroProbe nonzero))

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_positive_unary_source_zero
#print axioms V8NativeMessage.N7LiteralSupport.original_all_true_nonzero_requires_every_pin
#print axioms V8NativeMessage.N7LiteralSupport.actual_geometric_capacity_excludes_original_slot
