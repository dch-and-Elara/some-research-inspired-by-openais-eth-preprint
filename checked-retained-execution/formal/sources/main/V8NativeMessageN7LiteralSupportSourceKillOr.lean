import V8NativeMessageN7LiteralSupportSourceKill

/-! The original old-row empty-support case caused by a completely
shiftless physical OR, independently of the other rows and pin signs. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9PacketTiles
open J6ActiveRun J6R12Blueprint J6R11Blueprint J6R9Recursive
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000
set_option maxRecDepth 2400
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)
local notation "E" => (DWire F)

def sourceOrPort (e : F) (b : Bool) : E := (.inr (.inl (e,b)),true)

theorem actual_shiftless_original_or_is_zero {R : Type} [CommRing R] {a : ℕ}
    (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) (e : F)
    (absent : ∀ b : Bool,¬ ∃ q : E,Matches P t (sourceOrPort F e b) q) :
    flatSigned P t κ (oldRowTruth F reg σ)=0 := by
  refine missing_required_inputs_kills_flat P t κ (oldRowTruth F reg σ)
    (.inl (.inr (.inr (.inl e)))) {sourceOrPort F e false,sourceOrPort F e true} ?_ ?_
  · intro r hr q cand
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with lr|rr
    · exact absent false ⟨q,lr ▸ cand⟩
    · exact absent true ⟨q,rr ▸ cand⟩
  · intro w off
    change (w (.inl (sourceOrPort F e false)) || w (.inl (sourceOrPort F e true)))=false
    rw [off _ (by simp),off _ (by simp)]
    rfl

variable {f : ℤ[X]} (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

theorem literal_original_shiftless_or_excludes_every_sign
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (zeroProbe : siteProbe F reg d x.1 x.2.1=0) (e : F)
    (absent : ∀ b : Bool,¬ ∃ q : E,Matches P x.1.val (sourceOrPort F e b) q) :
    wholePublic F reg P d hf σ x=0 := by
  rw [original_public_full_zero_probe F reg P d hf hd _ x zeroProbe]
  split
  · rw [exactZero,full_signed_root_is_zero_polynomial,full_root_at_zero_has_literal_two_cubes P
      (PublicIndex F reg f d x.1) (centerNonzero x.1) rfl,
      actual_shiftless_original_or_is_zero F reg P _ _ σ e absent,map_zero]
  · rfl

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_shiftless_original_or_is_zero
#print axioms V8NativeMessage.N7LiteralSupport.literal_original_shiftless_or_excludes_every_sign
