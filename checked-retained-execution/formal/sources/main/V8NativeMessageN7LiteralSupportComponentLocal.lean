import V8NativeMessageN7LiteralSupportComponentFactor
import V8NativeMessageN7LiteralSupportOrientation

/-! Source pin-sign locality for the genuine components, with a direct
two-colour cut that cannot break an actual shifted matched edge. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option maxRecDepth 2300
noncomputable section

section Mark
variable {E A B G : Type} [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B} (P : PhysicalPacking N a G)

def markComponent (t : ℤ) (root v : A⊕B) : Bool := decide (Connected P t root v)

theorem matches_keep_mark (t : ℤ) (root : A⊕B) {r q : E} (h : Matches P t r q) :
    markComponent P t root (.inl (N.row r)) =
    markComponent P t root (.inr (N.col q)) := by
  unfold markComponent
  apply decide_eq_decide.mpr
  have m := true_match_connects_actual_endpoints P h
  exact ⟨fun hx=>Relation.EqvGen.trans _ _ _ hx m,
    fun hx=>Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.symm _ _ m)⟩

theorem mark_connected_iff (t : ℤ) (root v : A⊕B) :
    markComponent P t root v=true ↔ Connected P t root v := by
  unfold markComponent
  exact decide_eq_true_iff

end Mark

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)

def oldUnaryVertex (v : W) : DOld F⊕MainClonedCNF.Port F := .inl (.inr (.inl v))

private theorem old_gate_depends_on_its_one_possible_pin (σ τ : W→Bool)
    (u : DOld F⊕MainClonedCNF.Port F) (x : ParentPorts N u→Bool)
    (same : ∀v : W,u=oldUnaryVertex F v→σ v=τ v) :
    oldRowTruth F reg σ u x=oldRowTruth F reg τ u x := by
  rcases u with (k|w|e|c)|q
  · rfl
  · simp only [oldRowTruth,same w rfl]
  · rfl
  · rfl
  · rfl

theorem actual_old_component_factor_is_sign_local
    {a : ℕ} {R K : Type} [CommRing R] [Fintype K]
    (P : PhysicalPacking (dNetwork F reg) a (Fin 64))
    (t : ℤ) (color : DOld F⊕MainClonedCNF.Port F→K) (k : K) (σ τ : W→Bool)
    (same : ∀ v : W,color (oldUnaryVertex F v)=k→σ v=τ v) :
    (literalComponentFactors P t color (oldRowTruth F reg σ) k : R) =
      literalComponentFactors P t color (oldRowTruth F reg τ) k := by
  unfold literalComponentFactors localSum
  refine Finset.sum_congr rfl fun y _=>Finset.prod_congr rfl fun u _=>?_
  apply congrArg (bit R)
  apply old_gate_depends_on_its_one_possible_pin F reg σ τ
  intro v e
  apply same
  rw [←e]
  exact u.property

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.matches_keep_mark
#print axioms V8NativeMessage.N7LiteralSupport.mark_connected_iff
#print axioms V8NativeMessage.N7LiteralSupport.actual_old_component_factor_is_sign_local
