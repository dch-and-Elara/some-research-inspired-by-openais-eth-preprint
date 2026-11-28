import V8NativeMessageN7LiteralSupportOrientation
import J6BlockFactor

/-! Literal row scopes of the four-clone network: a unary port, either
ordered binary clause, and the three actual variable occurrences. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial
open Polynomial J6R10Repack J1MainSourceCollision
open Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
set_option maxRecDepth 1900
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)

abbrev LiteralRowScope (u : DOld F) := J6BlockFactor.rows (N).row u

def pinScope (v : W) : Unit ≃ LiteralRowScope F reg (.inr (.inl v)) where
  toFun _ := ⟨(.inl v,true),rfl⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨p,b⟩,h⟩
    apply Subtype.ext
    cases b
    · simp [dNetwork] at h
    · rcases p with q|q
      · have : q=v := by simpa [dNetwork,cloneFactor] using h
        subst q
        rfl
      · rcases q with q|q <;> simp [dNetwork,cloneFactor] at h

def clauseScope (e : F) : Bool ≃ LiteralRowScope F reg (.inr (.inr (.inl e))) where
  toFun b := ⟨(.inr (.inl (e,b)),true),rfl⟩
  invFun p :=
    match p.val.1 with
    | .inr (.inl (_,b)) => b
    | _ => false
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨p,b⟩,h⟩
    apply Subtype.ext
    cases b
    · simp [dNetwork] at h
    · rcases p with q|(⟨q,j⟩|q)
      · simp [dNetwork,cloneFactor] at h
      · have : q=e := by simpa [dNetwork,cloneFactor] using h
        subst q
        rfl
      · simp [dNetwork,cloneFactor] at h

def impScope (v : W) (j : Fin 4) : Bool ≃ LiteralRowScope F reg (.inr (.inr (.inr (v,j)))) where
  toFun b := ⟨(.inr (.inr (v,j,b)),true),rfl⟩
  invFun p :=
    match p.val.1 with
    | .inr (.inr (_,_,b)) => b
    | _ => false
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨p,b⟩,h⟩
    apply Subtype.ext
    cases b
    · simp [dNetwork] at h
    · rcases p with q|(q|⟨u,k,c⟩)
      · simp [dNetwork,cloneFactor] at h
      · simp [dNetwork,cloneFactor] at h
      · have hh : (u,k)=(v,j) := by
          have same := Sum.inr.inj (Sum.inr.inj h)
          exact Sum.inr.inj same
        have hv := congrArg Prod.fst hh
        have hj := congrArg Prod.snd hh
        change u=v at hv
        change k=j at hj
        subst u k
        rfl

def cloneScope (v : Clone W) : varFibre (cloneOwner F reg) v ≃ LiteralRowScope F reg (.inl v) where
  toFun q := ⟨(q.val,false), by
    change Sum.inl (cloneOwner F reg q.val)=_
    exact congrArg Sum.inl (Finset.mem_filter.mp q.property).2⟩
  invFun p := ⟨p.val.1, by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    obtain ⟨⟨p,b⟩,h⟩ := p
    cases b
    · exact Sum.inl.inj h
    · cases h⟩
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨⟨p,b⟩,h⟩ := p
    apply Subtype.ext
    cases b
    · rfl
    · cases h

theorem actual_clone_scope_card (v : Clone W) :
    Fintype.card (LiteralRowScope F reg (.inl v))=3 := by
  rw [←Fintype.card_congr (cloneScope F reg v),Fintype.card_coe]
  exact every_clone_three F reg v

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.pinScope
#print axioms V8NativeMessage.N7LiteralSupport.clauseScope
#print axioms V8NativeMessage.N7LiteralSupport.impScope
#print axioms V8NativeMessage.N7LiteralSupport.cloneScope
#print axioms V8NativeMessage.N7LiteralSupport.actual_clone_scope_card
