import V8NativeMessageN7LiteralSupportComponentLocal
import V8NativeMessageN6DSupport

/-! The literal four-clone target exterior pair must remain in one
real rewired component if a zero-mode parity contraction equals UD
on all sign words. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles DenominatorBudget
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
set_option maxRecDepth 2500
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀ v,GraphCutMoments.degree E v=3)
variable (loopless : ∀ v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "hF" => replaced_cubic E baseCubic loopless
variable {a : ℕ}

theorem true_old_row_exterior_pair_in_same_wiring_component
    (P : PhysicalPacking (dNetwork (replacedEdges E baseCubic)
      (replaced_cubic E baseCubic loopless)) a (Fin 64))
    (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (mem : t∈P1DyadicGrid.grid a)
    {R : Type} [CommRing R] [Nontrivial R] (φ : TwoLocal→+*R) (h2 : (2:R)=0)
    (exactParity : ∀ σ,φ (exactZero P i t (oldRowTruth F hF σ))=UD E baseCubic R σ)
    (e : E) :
    Connected P t (oldUnaryVertex F (seat E baseCubic e false))
      (oldUnaryVertex F (seat E baseCubic e true)) := by
  let root := oldUnaryVertex F (seat E baseCubic e false)
  let color := markComponent P t root
  let value (k : Bool) (σ : TriVertex V→Bool) : R :=
    literalComponentFactors P t color (oldRowTruth F hF σ) k
  have hc (σ : TriVertex V→Bool) : (∏ k,value k σ)=UD E baseCubic R σ :=
    (factor_actual_parity_wiring P i ht hv mem φ h2 color (fun h=>matches_keep_mark P t root h) _).symm.trans
      (exactParity σ)
  have scope : UsesOnly (fun v=>color (oldUnaryVertex F v)) value := by
    intro k σ τ same
    exact actual_old_component_factor_is_sign_local F hF P t color k σ τ same
  have equal := exterior_pair_same_group E baseCubic (fun v=>color (oldUnaryVertex F v))
    value scope hc e
  have r : color root=true := (mark_connected_iff P t root root).mpr (Relation.EqvGen.refl _)
  exact (mark_connected_iff P t root _).mp (equal.symm.trans r)

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.true_old_row_exterior_pair_in_same_wiring_component
