import V8NativeMessageN7LiteralSupportComponentLocal

/-! The opposite genuine orientation reads sign words only on the
old unary column vertices of its own real rewired component. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 2400
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)

def oldUnaryColumn (v : W) : MainClonedCNF.Port F⊕DOld F := .inr (.inr (.inl v))

private theorem old_column_gate_depends_on_its_one_possible_pin (σ τ : W→Bool)
    (u : MainClonedCNF.Port F⊕DOld F) (x : ParentPorts (oldColumnNetwork F reg) u→Bool)
    (same : ∀v : W,u=oldUnaryColumn F v→σ v=τ v) :
    oldColumnTruth F reg σ u x=oldColumnTruth F reg τ u x := by
  rcases u with q|(k|w|e|c)
  · rfl
  · rfl
  · rw [unary_column_literal,unary_column_literal,same w rfl]
  · rfl
  · rfl

theorem actual_old_column_component_factors_are_sign_local
    {a : ℕ} {R K : Type} [CommRing R] [Fintype K]
    (P : PhysicalPacking (oldColumnNetwork F reg) a (Fin 64))
    (t : ℤ) (color : (MainClonedCNF.Port F⊕DOld F)→K) (k : K) (σ τ : W→Bool)
    (same : ∀ v : W,color (oldUnaryColumn F v)=k→σ v=τ v) :
    (literalComponentFactors P t color (oldColumnTruth F reg σ) k : R) =
      literalComponentFactors P t color (oldColumnTruth F reg τ) k := by
  unfold literalComponentFactors localSum
  refine Finset.sum_congr rfl fun y _=>Finset.prod_congr rfl fun u _=>?_
  apply congrArg (bit R)
  apply old_column_gate_depends_on_its_one_possible_pin F reg σ τ
  intro v e
  apply same
  rw [←e]
  exact u.property

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_old_column_component_factors_are_sign_local
