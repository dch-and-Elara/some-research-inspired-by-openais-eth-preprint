import J6BlockFactor

/-! Enumerating actual local bits by their owner.  No connectedness is
assumed here; the resulting partition identity can later be applied to
true connected components, or to a cut by one component. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000
noncomputable section

variable {K I J X R : Type} [Fintype K] [Fintype I] [Fintype J] [Fintype X] [CommRing R]

abbrev Fiber (part : I→K) (k : K) := J6BlockFactor.rows part k

def fiberWord (part : I→K) : (I→X) ≃ (∀ k,Fiber part k→X) where
  toFun w _ i := w i.val
  invFun w i := w (part i) ⟨i,rfl⟩
  left_inv _ := rfl
  right_inv w := by
    funext k i
    obtain ⟨i,e⟩ := i
    subst k
    rfl

def fillFiber (part : I→K) (k : K) (default : X) (x : Fiber part k→X) (i : I) : X :=
  if h : part i=k then x ⟨i,h⟩ else default

omit [Fintype K] [Fintype I] [Fintype X] in
theorem fillFiber_roundtrip (part : I→K) (k : K) (d : X) (w : I→X)
    (i : I) (h : part i=k) : fillFiber part k d (fun j=>w j.val) i = w i := by
  rw [fillFiber,dif_pos h]

def localSum (inPart : I→K) (outPart : J→K) (d : X) (f : J→(I→X)→R) (k : K) : R :=
  ∑ w : Fiber inPart k→X, ∏ j : Fiber outPart k, f j.val (fillFiber inPart k d w)

theorem split_actual_bits (inPart : I→K) (outPart : J→K) (d : X)
    (f : J→(I→X)→R)
    (locality : ∀ j w w', (∀ i,inPart i=outPart j→w i=w' i)→f j w=f j w') :
    (∑ w : I→X,∏ j,f j w)=∏ k,localSum inPart outPart d f k := by
  let W (k : K) (u : Fiber inPart k→X) :=
    ∏ j : Fiber outPart k, f j.val (fillFiber inPart k d u)
  change _ = ∏ k,∑ u,W k u
  rw [Fintype.prod_sum (κ:=fun k=>Fiber inPart k→X) W]
  refine Fintype.sum_equiv (fiberWord inPart) _ _ fun w=>?_
  rw [J6BlockFactor.prod_rows outPart (fun j=>f j w)]
  refine Finset.prod_congr rfl fun k _=>Finset.prod_congr rfl fun j _=>?_
  apply locality
  intro i hi
  have eq : inPart i=k := hi.trans j.property
  exact (fillFiber_roundtrip inPart k d w i eq).symm

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.fillFiber_roundtrip
#print axioms V8NativeMessage.N7LiteralSupport.split_actual_bits
