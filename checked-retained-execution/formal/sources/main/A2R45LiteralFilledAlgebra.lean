
import Acquisition
import J6R10IntegralDeformation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 16
set_option linter.unusedSectionVars false

/-! Algebraic bridge from a physically filled star chart to the already
checked paired-register identity. The even and padding rows are genuine
summands with all-one tables, and their lag sums are eliminated, not
silently removed from the graph. -/
namespace A2R45Literal
open scoped Classical BigOperators
open Acquisition
noncomputable section

variable {I Pad K : Type*} [Fintype I] [Fintype Pad]
    [DecidableEq I] [DecidableEq Pad] [CommRing K]

abbrev Filled (I Pad : Type*) := (I×Bool)⊕Pad
abbrev Bits (I Pad : Type*) := Filled I Pad→Bool
abbrev Parts (I Pad : Type*) := (I→Bool)×(I→Bool)×(Pad→Bool)
def evenBits (x : Bits I Pad) : I→Bool := fun i=>x (.inl (i,false))
def oddBits (x : Bits I Pad) : I→Bool := fun i=>x (.inl (i,true))
def spareBits (x : Bits I Pad) : Pad→Bool := fun i=>x (.inr i)

def assemble (w : Parts I Pad) : Bits I Pad
  | .inl (i,false) => w.1 i
  | .inl (i,true) => w.2.1 i
  | .inr p => w.2.2 p

def splitAssignment : Bits I Pad≃Parts I Pad where
  toFun x := (evenBits x,oddBits x,spareBits x)
  invFun := assemble
  left_inv x := by
    funext i
    rcases i with ⟨i,b⟩|i
    · cases b <;> rfl
    · rfl
  right_inv _ := rfl

def evenArgs (a : Filled I Pad→K) : I→K := fun i=>a (.inl (i,false))
def oddArgs (a : Filled I Pad→K) : I→K := fun i=>a (.inl (i,true))
def spareArgs (a : Filled I Pad→K) : Pad→K := fun i=>a (.inr i)

def lagProduct {Z : Type*} [Fintype Z] (a : Z→K) (x : Z→Bool) : K :=
  ∏ i : Z,lag (x i) (a i)

theorem split_lag_product (a : Filled I Pad→K) (x : Bits I Pad) :
    lagProduct a x=lagProduct (evenArgs a) (evenBits x)*
      lagProduct (oddArgs a) (oddBits x)*lagProduct (spareArgs a) (spareBits x) := by
  unfold lagProduct
  rw [Fintype.prod_sum_type,Fintype.prod_prod_type,Finset.prod_comm,Fintype.prod_bool]
  exact congrArg (· * ∏ i : Pad, lag (x (.inr i)) (a (.inr i)))
    (mul_comm _ _)

private theorem sum_lag_is_one {Z : Type*} [Fintype Z] [DecidableEq Z] (a : Z→K) :
    ∑ x : Z→Bool,lagProduct a x=1 := by
  simpa only [extension,one_mul,lagProduct] using extension_one a

theorem extension_ignores_dummy_rows (a : Filled I Pad→K) (row : (I→Bool)→K) :
    extension (row ∘ oddBits (I:=I) (Pad:=Pad)) a=extension row (oddArgs a) := by
  let U := lagProduct (evenArgs a)
  let V := lagProduct (oddArgs a)
  let W := lagProduct (spareArgs a)
  have hU : ∑ x : I→Bool,U x=1 := sum_lag_is_one _
  have hW : ∑ x : Pad→Bool,W x=1 := sum_lag_is_one _
  calc
    _ = ∑ p : Parts I Pad,row p.2.1*(U p.1*V p.2.1*W p.2.2) := by
      unfold extension
      apply Fintype.sum_equiv (splitAssignment (I:=I) (Pad:=Pad))
      intro y
      change row (oddBits y)*lagProduct a y=_
      rw [split_lag_product]
      rfl
    _ = ∑ x : I→Bool,U x * ∑ y : I→Bool,(row y*V y)*(∑ z : Pad→Bool,W z) := by
      simp only [Fintype.sum_prod_type,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      rw [hW]
      simp only [mul_one,←Finset.sum_mul,hU,one_mul]
      rfl

def actualArgument (M : Filled I Pad→Filled I Pad→K) (x : Bits I Pad) (i : Filled I Pad) : K :=
  ∑ j : Filled I Pad,if x j then M i j else 0

def sourceColumns (col : (I→Bool)→K) (x : Bits I Pad) : K :=
  col (evenBits x)*pinsZero (oddBits x)*pinsZero (spareBits x)

private theorem lag_if (b : Bool) (a : K) : lag b a=(if b then a else 1-a) := by
  cases b <;> rfl

theorem filled_contract_eq_shifted (M : Filled I Pad→Filled I Pad→K)
    (row col : (I→Bool)→K)
    (hr : ∀ x : Bits I Pad,∀ i : I,
      actualArgument M x (.inl (i,true))=-bit (x (.inl (i,false)))) :
    J6R10Integral.contract M (row ∘ oddBits) (sourceColumns col)=
      ∑ x : I→Bool,col x*extension row (fun i=>-bit (x i)) := by
  unfold J6R10Integral.contract
  rw [Finset.sum_comm]
  calc
    _ = ∑ x : Bits I Pad,sourceColumns col x*
        extension (row ∘ oddBits (I:=I) (Pad:=Pad)) (actualArgument M x) := by
      apply Finset.sum_congr (by ext x; simp only [Finset.mem_univ])
      intro x _
      rw [extension,Finset.mul_sum]
      apply Finset.sum_congr (by ext y; simp only [Finset.mem_univ])
      intro y _
      simp only [actualArgument,lag_if]
      ring
    _ = ∑ x : Bits I Pad,sourceColumns col x*
        extension row (fun i=>-bit (evenBits x i)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [extension_ignores_dummy_rows]
      have hfun : oddArgs (actualArgument M x)=(fun i=>-bit (evenBits x i)) :=
        funext (hr x)
      rw [hfun]
    _ = ∑ p : Parts I Pad,
        (col p.1*pinsZero p.2.1*pinsZero p.2.2)*
        extension row (fun i=>-bit (p.1 i)) := by
      apply Fintype.sum_equiv (splitAssignment (I:=I) (Pad:=Pad))
      intro x
      rfl
    _ = _ := by
      simp only [Fintype.sum_prod_type,pinsZero_eq,apply_ite,ite_mul,mul_zero,zero_mul,
        mul_one,Fintype.sum_ite_eq']

#print axioms split_lag_product
#print axioms extension_ignores_dummy_rows
#print axioms filled_contract_eq_shifted
end
end A2R45Literal
