import V8R45PooledLiteralOrigin

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
set_option maxRecDepth 2400

namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu.FiveCopy
open P11FullPacking J6R10Repack J6R11Repack J6R11Blueprint J6R12Blueprint

variable {V E : Type} [Fintype V] [Fintype E]
variable (G : Graph V E) (p : ThreePorts G)

def clauseWireChart (i : ClauseId V E) :
    {e : Edge V E // (network G p).row e = .inl i} ≃ Bool where
  toFun e := e.val.1.2
  invFun b := ⟨((i,b),false),rfl⟩
  left_inv := by
    rintro ⟨⟨⟨q,b⟩,d⟩,h⟩
    cases d
    · have he : q=i := Sum.inl.inj h
      subst q
      rfl
    · exact (Sum.noConfusion h)
  right_inv _ := rfl

def variableWireChart (v : Variable V) :
    {e : Edge V E // (network G p).row e = .inr v} ≃ VarInc G p v where
  toFun := by
    rintro ⟨⟨q,d⟩,h⟩
    cases d
    · exact (Sum.noConfusion h)
    · exact ⟨q,Sum.inr.inj h⟩
  invFun e := ⟨(e.val,true),congrArg Sum.inr e.property⟩
  left_inv := by
    rintro ⟨⟨q,d⟩,h⟩
    cases d
    · exact (Sum.noConfusion h)
    · rfl
  right_inv := fun _ => rfl

def subdivWireChart (q : Occ V E) :
    {e : Edge V E // (network G p).col e = q} ≃ Bool where
  toFun e := e.val.2
  invFun b := ⟨(q,b),rfl⟩
  left_inv := by
    rintro ⟨⟨r,b⟩,h⟩
    change r=q at h
    subst r
    rfl
  right_inv _ := rfl

theorem literal_root_degree_three (f : ℤ[X]) (s : V → Bool) :
    GoodDegree (rawHost G p f s) 3 := by
  constructor
  · rintro (i|v)
    · change Nat.card {e : Edge V E // (network G p).row e = .inl i} ≤ 3
      rw [Nat.card_congr (clauseWireChart G p i),Nat.card_eq_fintype_card,Fintype.card_bool]
      decide
    · change Nat.card {e : Edge V E // (network G p).row e = .inr v} ≤ 3
      rw [Nat.card_congr (variableWireChart G p v)]
      have h := variable_degree G p (fun _ => false) v
      change Nat.card (VarInc G p v) = _ at h
      rw [h]
      cases v <;> simp
  · intro q
    change Nat.card {e : Edge V E // (network G p).col e = q} ≤ 3
    rw [Nat.card_congr (subdivWireChart G p q),Nat.card_eq_fintype_card,Fintype.card_bool]
    decide

#print axioms clauseWireChart
#print axioms variableWireChart
#print axioms subdivWireChart
#print axioms literal_root_degree_three
end V8R45PooledLiteral