import J8SourceMoment
import Mathlib.Data.Fintype.BigOperators

/-! The actual old two-port equality tensor, after independently
summing its two retained row bits. At the singleton target leg use
the real affine slope; all other row legs use their actual baseline. -/
namespace J6R14SpecializedBox
open scoped BigOperators Classical
open J8SourceMoment LiteralPortCompiler

noncomputable section
variable {K : Type*} [CommRing K]

def selectLeg (mark : Option Bool) (leg : Bool) (bit : Bool) (base : K) : K :=
  if mark = some leg then slope bit else affine bit base

def boolPair : (Bool→Bool) ≃ Bool×Bool where
  toFun y := (y false,y true)
  invFun y := twoBits y.1 y.2
  left_inv y := by funext b; cases b <;> rfl
  right_inv _ := rfl

theorem pair_sum_rowFactor (mark : Option Bool) (a b : K) :
    (∑ y : Bool→Bool, (truth (equality false true) y : K) *
      (selectLeg mark false (y false) a * selectLeg mark true (y true) b)) =
      rowFactor mark a b := by
  let F (y : Bool×Bool) : K :=
    (truth (equality false true) (twoBits y.1 y.2) : K) *
      (selectLeg mark false y.1 a * selectLeg mark true y.2 b)
  calc
    _ = ∑ y : Bool×Bool, F y := by
      apply Fintype.sum_equiv boolPair
      intro x
      change _ = (truth (equality false true) (twoBits (x false) (x true)) : K) * _
      have h : twoBits (x false) (x true) = x := by funext j; cases j <;> rfl
      rw [h]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      cases mark with
      | none => simp [F,selectLeg,rowFactor,oldEquality]
      | some leg =>
          cases leg <;> simp [F,selectLeg,rowFactor,selectedEquality]

def curryRows (I : Type*) : ((I×Bool)→Bool) ≃ (I→Bool→Bool) where
  toFun y i j := y (i,j)
  invFun y d := y d.1 d.2
  left_inv y := by funext d; cases d; rfl
  right_inv _ := rfl

theorem contract_marked_rows {I : Type*} [Fintype I] (mark : Option (I×Bool))
    (base : I→Bool→K) :
    (∑ y : (I×Bool)→Bool,
      ∏ i : I, (truth (equality false true) (fun b => y (i,b)) : K) *
        (selectLeg (marker mark i) false (y (i,false)) (base i false) *
         selectLeg (marker mark i) true (y (i,true)) (base i true))) =
    ∏ i : I, rowFactor (marker mark i) (base i false) (base i true) := by
  let W (i : I) (y : Bool→Bool) : K :=
    (truth (equality false true) y : K) *
      (selectLeg (marker mark i) false (y false) (base i false) *
       selectLeg (marker mark i) true (y true) (base i true))
  calc
    _ = ∑ y : I→Bool→Bool, ∏ i : I, W i (y i) :=
      Fintype.sum_equiv (curryRows I) _ _ (fun _ => rfl)
    _ = ∏ i : I, ∑ y : Bool→Bool, W i y := (Fintype.prod_sum W).symm
    _ = _ := by simp only [W,pair_sum_rowFactor]

#print axioms pair_sum_rowFactor
#print axioms contract_marked_rows
end
end J6R14SpecializedBox
