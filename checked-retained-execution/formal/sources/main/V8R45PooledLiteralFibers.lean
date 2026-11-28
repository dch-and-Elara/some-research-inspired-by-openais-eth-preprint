import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finite.Prod

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 2200

/-! Measure only states actually obtainable over each fixed menu. An
ambient advice type may be larger, or even infinite. -/
namespace V8R45PooledLiteral
open scoped Classical
noncomputable section
variable {X M : Type*} {Side : M → Type*}
variable (mnu : X → M) (aux : ∀ x, Side (mnu x))

abbrev UsedSide (m : M) :=
  {a : Side m // ∃ (x : X) (h : mnu x=m), a=cast (congrArg Side h) (aux x)}

def visitToState (m : M) (x : {x : X // mnu x=m}) : UsedSide mnu aux m :=
  ⟨cast (congrArg Side x.property) (aux x.val),⟨x.val,x.property,rfl⟩⟩

theorem visit_to_state_surjective (m : M) : Function.Surjective (visitToState mnu aux m) := by
  rintro ⟨a,x,h,e⟩
  exact ⟨⟨x,h⟩,Subtype.ext e.symm⟩

def usedSideFintype [Finite X] (m : M) : Fintype (UsedSide mnu aux m) := by
  letI : Finite (UsedSide mnu aux m) :=
    Finite.of_surjective _ (visit_to_state_surjective mnu aux m)
  exact Fintype.ofFinite _

def usedState (x : X) : UsedSide mnu aux (mnu x) :=
  visitToState mnu aux (mnu x) ⟨x,rfl⟩

theorem used_state_exact (x : X) : (usedState mnu aux x).val = aux x := rfl

#print axioms visit_to_state_surjective
#print axioms usedSideFintype
#print axioms used_state_exact
end
end V8R45PooledLiteral