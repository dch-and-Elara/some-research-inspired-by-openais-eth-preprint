import V8NativeMessageN7LiteralSupportComponentColumn
import V8NativeMessageN7LiteralSupportSourceKill
import V8NativeMessageN7LiteralSupportScopes

/-! An unmatched true unary column is isolated in the rewired graph,
not merely unrepresented by a particular group. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000
set_option maxRecDepth 2300
noncomputable section

section Generic
variable {E A B G : Type} [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B} (P : PhysicalPacking N a G)

theorem no_incoming_real_match_isolates_column
    (t : ℤ) (v : B) (onlyWire : E)
    (unique : ∀ q,N.col q=v→q=onlyWire)
    (absent : ∀ r,¬Matches P t r onlyWire)
    {u : A⊕B} (h : Connected P t (.inr v) u) : u=.inr v := by
  let isV (x : A⊕B) : Prop := x=.inr v
  have uncut {r q : E} (m : Matches P t r q) :
      isV (.inl (N.row r)) = isV (.inr (N.col q)) := by
    have left : ¬isV (.inl (N.row r)) := fun h=>Sum.noConfusion h
    have right : ¬isV (.inr (N.col q)) := by
      intro s
      have e : q=onlyWire := unique q (Sum.inr.inj s)
      exact absent r (e ▸ m)
    exact propext ⟨fun h=>(left h).elim,fun h=>(right h).elim⟩
  have e := any_valid_component_class_preserved P t isV uncut h
  exact Eq.mp e rfl

end Generic

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)

omit [Fintype W] in
theorem original_unary_column_has_only_its_real_wire
    (v : W) (q : DWire F) (owner : (oldColumnNetwork F reg).col q=.inr (.inl v)) :
    q=sourceUnaryWire F v := by
  let p : LiteralRowScope F reg (.inr (.inl v)) := ⟨q,owner⟩
  let e := pinScope F reg v
  exact (congrArg Subtype.val (e.apply_symm_apply p)).symm

omit [Fintype W] in
theorem original_unmatched_old_column_is_isolated {a : ℕ}
    (P : PhysicalPacking (oldColumnNetwork F reg) a (Fin 64))
    (t : ℤ) (v : W)
    (absent : ∀ r,¬Matches P t r (sourceUnaryWire F v))
    {u : MainClonedCNF.Port F⊕DOld F} (h : Connected P t (oldUnaryColumn F v) u) :
    u=oldUnaryColumn F v :=
  no_incoming_real_match_isolates_column P t (.inr (.inl v)) (sourceUnaryWire F v)
    (original_unary_column_has_only_its_real_wire F reg v) absent h

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.no_incoming_real_match_isolates_column
#print axioms V8NativeMessage.N7LiteralSupport.original_unary_column_has_only_its_real_wire
#print axioms V8NativeMessage.N7LiteralSupport.original_unmatched_old_column_is_isolated
