import LiteralPortCompiler
import Mathlib.Tactic

/-! Exact finite sums of literal source affine factors on unary,
ordered binary and nonempty constant-equality truth tables. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000
noncomputable section

def cubeWeighted {I R : Type} [Fintype I] [CommRing R] (A : (I→Bool)→Bool) (b : I→R) : R :=
  ∑ w : I→Bool, if A w then ∏ j,LiteralPortCompiler.affine (w j) (b j) else 0

private def pairWordEquiv : (Bool→Bool) ≃ Bool×Bool where
  toFun w := (w false,w true)
  invFun x b := if b then x.2 else x.1
  left_inv _ := by funext b; cases b <;> rfl
  right_inv _ := rfl

private def unitWordEquiv : (Unit→Bool) ≃ Bool where
  toFun w := w ()
  invFun b _ := b
  left_inv _ := by funext u; cases u; rfl
  right_inv _ := rfl

variable {R : Type} [CommRing R]

theorem literal_unary_eval (s : Bool) (x : R) :
    cubeWeighted (fun w : Unit→Bool=>decide (w ()=s)) (fun _=>x) =
      LiteralPortCompiler.affine s x := by
  unfold cubeWeighted
  let f (b : Bool) : R := if b=s then LiteralPortCompiler.affine b x else 0
  have conv (w : Unit→Bool) :
      (if decide (w ()=s) then ∏ j : Unit,LiteralPortCompiler.affine (w j) x else 0)=
        f (unitWordEquiv w) := by simp [f,unitWordEquiv]
  calc
    _ = ∑ b : Bool,f b := by
      refine Eq.trans ?_ (Fintype.sum_equiv unitWordEquiv _ f conv)
      exact Finset.sum_congr (Finset.ext fun _=>by simp only [Finset.mem_univ]) (fun _ _=>rfl)
    _ = _ := by
      rw [Fintype.sum_bool]
      cases s <;> simp [f]

theorem literal_or_eval (x y : R) :
    cubeWeighted (fun w : Bool→Bool=>w false||w true) (fun j=>if j then y else x)=
      x+y-x*y := by
  unfold cubeWeighted
  let f (b : Bool×Bool) := if b.1||b.2 then
    LiteralPortCompiler.affine b.1 x*LiteralPortCompiler.affine b.2 y else 0
  have eq (w : Bool→Bool) :
      (if w false||w true then ∏ j : Bool,LiteralPortCompiler.affine (w j) (if j then y else x)
        else 0)=f (pairWordEquiv w) := by
    rw [Fintype.prod_bool,mul_comm]
    rfl
  calc
    _ = ∑ b : Bool×Bool,f b := by
      refine Eq.trans ?_ (Fintype.sum_equiv pairWordEquiv _ f eq)
      exact Finset.sum_congr (Finset.ext fun _=>by simp only [Finset.mem_univ]) (fun _ _=>rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [f,LiteralPortCompiler.affine]
      ring

theorem literal_imp_eval (x y : R) :
    cubeWeighted (fun w : Bool→Bool=>!(w false)||w true) (fun j=>if j then y else x) =
      1-x+x*y := by
  unfold cubeWeighted
  let f (b : Bool×Bool) := if !b.1||b.2 then
    LiteralPortCompiler.affine b.1 x*LiteralPortCompiler.affine b.2 y else 0
  have eq (w : Bool→Bool) :
      (if !(w false)||w true then ∏ j : Bool,LiteralPortCompiler.affine (w j) (if j then y else x)
        else 0)=f (pairWordEquiv w) := by
    rw [Fintype.prod_bool,mul_comm]
    rfl
  calc
    _ = ∑ b : Bool×Bool,f b := by
      refine Eq.trans ?_ (Fintype.sum_equiv pairWordEquiv _ f eq)
      exact Finset.sum_congr (Finset.ext fun _=>by simp only [Finset.mem_univ]) (fun _ _=>rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [f,LiteralPortCompiler.affine]
      ring

theorem literal_const_eval {I : Type} [Fintype I] [Nonempty I] (b : I→R) :
    cubeWeighted (fun w=>decide (∀ p q,w p=w q)) b =
      (∏ j,(1-b j))+(∏ j,b j) := by
  classical
  let a : I := Classical.choice inferInstance
  let u (b : Bool) : I→Bool := fun _=>b
  have ne : u false≠u true := fun e=>Bool.noConfusion (congrFun e a)
  let f (w : I→Bool) : R :=
    if ∀ p q,w p=w q then ∏ j,LiteralPortCompiler.affine (w j) (b j) else 0
  have eq : (∑ w,f w)=∑ w∈({u false,u true}:Finset (I→Bool)),f w := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w _ h
    unfold f
    apply if_neg
    intro hconst
    have e : w=u (w a) := funext fun i => hconst i a
    cases c : w a <;> rw [c] at e
    · exact h (by simp [e])
    · exact h (by simp [e])
  calc
    _ = (∑ w,f w) := by
      unfold cubeWeighted
      apply Finset.sum_congr (Finset.ext fun _=>by simp only [Finset.mem_univ])
      intro w _
      by_cases h : ∀ p q,w p=w q <;> simp [f,h]
    _ = _ := by
      rw [eq,Finset.sum_insert (by simp [ne]),Finset.sum_singleton]
      simp [f,u,LiteralPortCompiler.affine]


end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.literal_unary_eval
#print axioms V8NativeMessage.N7LiteralSupport.literal_or_eval
#print axioms V8NativeMessage.N7LiteralSupport.literal_imp_eval
#print axioms V8NativeMessage.N7LiteralSupport.literal_const_eval