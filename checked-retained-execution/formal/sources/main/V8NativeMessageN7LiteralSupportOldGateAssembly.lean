import V8NativeMessageN7LiteralSupportOldRows
import V8NativeMessageN7LiteralSupportScopes
import V8NativeMessageN7LiteralSupportLocal
import V8NativeMessageN7LiteralSupportFiniteGateSums
import V8NativeMessageN7LiteralSupportSupportCore
import V8NativeMessageN7LiteralSupportOddSign
import V8NativeMessageN7LiteralSupportZero

/-! Exact per-row interpolation after eliminating all row assignments,
with equations on the original unary and ordered binary row scopes. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 2200
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)
local notation "E" => (DWire F)
variable {R : Type} [CommRing R]

def rowScopeRead (u : DOld F) (w : LiteralRowScope F reg u→Bool)
    (p : ParentPorts N (.inl u)) : Bool :=
  match p with
  | ⟨.inl r,h⟩ => w ⟨r,Sum.inl.inj h⟩
  | ⟨.inr _,h⟩ => (Sum.noConfusion h : False).elim

def literalGateCube (u : DOld F) (σ : W→Bool) (b : E→R) : R :=
  ∑ w : LiteralRowScope F reg u→Bool,
    if oldRowTruth F reg σ (.inl u) (rowScopeRead F reg u w) then
      ∏ r : LiteralRowScope F reg u,LiteralPortCompiler.affine (w r) (b r.val) else 0

theorem actual_row_factor_is_local_gate_cube (u : DOld F) (σ : W→Bool) (b : E→R) :
    literalRowFactor F reg σ b u=literalGateCube F reg u σ b := by
  unfold literalRowFactor genericRowFactor localSum literalGateCube
  refine Finset.sum_congr rfl fun w _=>?_
  let u₀ : Fiber (id : DOld F→DOld F) u := ⟨u,rfl⟩
  have singleton : (Finset.univ : Finset (Fiber (id : DOld F→DOld F) u))={u₀} := by
    ext j
    have eq : j=u₀ := Subtype.ext j.property
    simp only [eq,Finset.mem_univ,Finset.mem_singleton]
  rw [singleton,Finset.prod_singleton,genericRowTerm]
  have readEq : (fun p : ParentPorts N (.inl u)=>fillFiber (N).row u false w (edge p.val)) =
      rowScopeRead F reg u w := by
    funext p
    obtain ⟨p,h⟩ := p
    cases p with
    | inl r =>
      change fillFiber (N).row u false w r=w ⟨r,Sum.inl.inj h⟩
      rw [fillFiber,dif_pos (Sum.inl.inj h)]
    | inr c => cases h
  rw [readEq]
  have eqWeight (r : LiteralRowScope F reg u) : fillFiber (N).row u false w r.val = w r := by
    rw [fillFiber,dif_pos r.property]
    exact congrArg w (Subtype.ext rfl)
  simp only [eqWeight]
  cases oldRowTruth F reg σ (.inl u) (rowScopeRead F reg u w) <;> simp [bit]
  exact Finset.prod_congr (Finset.ext fun _=>by simp only [Finset.mem_univ]) (fun _ _=>rfl)

private def transferScope {I J : Type} (c : I ≃ J) : (J→Bool) ≃ (I→Bool) where
  toFun w := w∘c
  invFun w := w∘c.symm
  left_inv w := by funext j; simp [Function.comp_def]
  right_inv w := by funext i; simp [Function.comp_def]

theorem local_gate_reindex {I : Type} [Fintype I] (u : DOld F)
    (c : I ≃ LiteralRowScope F reg u) (σ : W→Bool) (b : E→R)
    (A : (I→Bool)→Bool)
    (exactGate : ∀ w,oldRowTruth F reg σ (.inl u) (rowScopeRead F reg u w)=A (w∘c)) :
    literalRowFactor F reg σ b u=cubeWeighted A (fun j=>b (c j).val) := by
  rw [actual_row_factor_is_local_gate_cube,literalGateCube,cubeWeighted]
  refine Fintype.sum_equiv (transferScope c) _ _ fun w=>?_
  rw [exactGate]
  change (if A (w∘c) then ∏ r : LiteralRowScope F reg u,LiteralPortCompiler.affine (w r) (b r.val) else 0) =
    if A (w∘c) then ∏ j : I,LiteralPortCompiler.affine (w (c j)) (b (c j).val) else 0
  split
  · symm
    exact Fintype.prod_equiv c (fun j=>LiteralPortCompiler.affine (w (c j)) (b (c j).val))
      (fun r=>LiteralPortCompiler.affine (w r) (b r.val)) (fun _=>rfl)
  · rfl

theorem original_pin_as_unary_cube (v : W) (σ : W→Bool) (b : E→R) :
    literalRowFactor F reg σ b (.inr (.inl v)) =
    cubeWeighted (fun w : Unit→Bool=>decide (w ()=σ v)) (fun _=>b (.inl v,true)) := by
  exact local_gate_reindex F reg _ (pinScope F reg v) σ b _ (fun _=>rfl)

theorem original_or_as_binary_cube (e : F) (σ : W→Bool) (b : E→R) :
    literalRowFactor F reg σ b (.inr (.inr (.inl e))) =
    cubeWeighted (fun w : Bool→Bool=>w false||w true) (fun j=>b (.inr (.inl (e,j)),true)) := by
  exact local_gate_reindex F reg _ (clauseScope F reg e) σ b _ (fun _=>rfl)

theorem original_imp_as_binary_cube (v : W) (j : Fin 4) (σ : W→Bool) (b : E→R) :
    literalRowFactor F reg σ b (.inr (.inr (.inr (v,j)))) =
    cubeWeighted (fun w : Bool→Bool=>!(w false)||w true) (fun c=>b (.inr (.inr (v,j,c)),true)) := by
  exact local_gate_reindex F reg _ (impScope F reg v j) σ b _ (fun _=>rfl)

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_row_factor_is_local_gate_cube
#print axioms V8NativeMessage.N7LiteralSupport.local_gate_reindex
#print axioms V8NativeMessage.N7LiteralSupport.original_pin_as_unary_cube
#print axioms V8NativeMessage.N7LiteralSupport.original_or_as_binary_cube
#print axioms V8NativeMessage.N7LiteralSupport.original_imp_as_binary_cube

/-! Eliminate the last actual local row assignment loops, without
any gate-form assumptions about old-row or subdivision scopes. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 2400
noncomputable section

variable {R : Type} [CommRing R]

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)

theorem original_pin_eval (v : W) (σ : W→Bool) (b : DWire F→R) :
    literalRowFactor F reg σ b (.inr (.inl v))=LiteralPortCompiler.affine (σ v) (b (.inl v,true)) := by
  rw [original_pin_as_unary_cube,literal_unary_eval]

theorem original_or_eval (e : F) (σ : W→Bool) (b : DWire F→R) :
    literalRowFactor F reg σ b (.inr (.inr (.inl e))) =
      b (.inr (.inl (e,false)),true)+b (.inr (.inl (e,true)),true)-
        b (.inr (.inl (e,false)),true)*b (.inr (.inl (e,true)),true) := by
  rw [original_or_as_binary_cube]
  have eArg : (fun c : Bool=>b (.inr (.inl (e,c)),true))=
    (fun c : Bool=>if c then b (.inr (.inl (e,true)),true) else b (.inr (.inl (e,false)),true)) := by
    funext c
    cases c <;> rfl
  rw [eArg,literal_or_eval]

theorem original_imp_eval (v : W) (j : Fin 4) (σ : W→Bool) (b : DWire F→R) :
    literalRowFactor F reg σ b (.inr (.inr (.inr (v,j)))) =
      1-b (.inr (.inr (v,j,false)),true)+
        b (.inr (.inr (v,j,false)),true)*b (.inr (.inr (v,j,true)),true) := by
  rw [original_imp_as_binary_cube]
  have eArg : (fun c : Bool=>b (.inr (.inr (v,j,c)),true))=
    (fun c : Bool=>if c then b (.inr (.inr (v,j,true)),true) else b (.inr (.inr (v,j,false)),true)) := by
    funext c
    cases c <;> rfl
  rw [eArg,literal_imp_eval]

theorem original_clone_eval (v : Clone W) (σ : W→Bool) (b : DWire F→R) :
    literalRowFactor F reg σ b (.inl v) =
      (∏ r : LiteralRowScope F reg (.inl v),(1-b r.val))+
      (∏ r : LiteralRowScope F reg (.inl v),b r.val) := by
  rw [actual_row_factor_is_local_gate_cube]
  let I := LiteralRowScope F reg (.inl v)
  letI : Nonempty I := Fintype.card_pos_iff.mp (by
    change 0<Fintype.card (LiteralRowScope F reg (.inl v))
    rw [actual_clone_scope_card]; omega)
  have flags (w : I→Bool) :
      oldRowTruth F reg σ (.inl (.inl v)) (rowScopeRead F reg (.inl v) w)=
        decide (∀ p q,w p=w q) := by
    change decide (∀ p q : ParentPorts (dNetwork F reg) (.inl (.inl v)), rowScopeRead F reg (.inl v) w p=
      rowScopeRead F reg (.inl v) w q)=_
    apply decide_eq_decide.mpr
    constructor
    · intro h r s
      exact h ⟨.inl r.val, congrArg Sum.inl r.property⟩
        ⟨.inl s.val, congrArg Sum.inl s.property⟩
    · intro h r s
      obtain ⟨r,hr⟩ := r
      obtain ⟨s,hs⟩ := s
      cases r with
      | inr _ => cases hr
      | inl r =>
        cases s with
        | inr _ => cases hs
        | inl s => exact h ⟨r,Sum.inl.inj hr⟩ ⟨s,Sum.inl.inj hs⟩
  simp only [literalGateCube,flags]
  exact literal_const_eval fun r : I=>b r.val

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.original_pin_eval
#print axioms V8NativeMessage.N7LiteralSupport.original_or_eval
#print axioms V8NativeMessage.N7LiteralSupport.original_imp_eval
#print axioms V8NativeMessage.N7LiteralSupport.original_clone_eval
