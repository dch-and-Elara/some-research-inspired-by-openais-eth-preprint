
import Acquisition

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5800000
set_option maxRecDepth 2050
set_option linter.unusedSectionVars false

/-! Original v9 A2 (A3)--(A4), lines 2273--2289:
the exact binary table on 2d distinct ports, at arbitrary d, over
any commutative receiver. This is the local clause-or-equality gadget,
not a completed CNF layout/quotient assertion. -/
namespace A2R45Literal
open scoped Classical BigOperators
open Acquisition
noncomputable section
variable {I K : Type*} [Fintype I] [CommRing K]

def a3Tag (a b : Bool) : K := if a=b then 1 else 0

private theorem a3Tag_product (a b : I→Bool) :
    (∏ i : I,a3Tag (K:=K) (a i) (b i))=if a=b then 1 else 0 := by
  by_cases e : a=b
  · subst b
    simp [a3Tag]
  · rw [if_neg e]
    have h : ∃ i,a i≠b i := by
      by_contra g
      push_neg at g
      exact e (funext g)
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

def a3PairCube : ((I×Bool)→Bool)≃(I→Bool×Bool) where
  toFun w i := (w (i,false),w (i,true))
  invFun z ij := if ij.2 then (z ij.1).2 else (z ij.1).1
  left_inv w := by
    funext i
    rcases i with ⟨i,j⟩
    cases j <;> rfl
  right_inv _ := rfl

def a3And (z : I→Bool×Bool) : I→Bool := fun i=>(z i).1&&(z i).2

def a3Table (b : (I→Bool)→Bool) (w : (I×Bool)→Bool) : Bool :=
  b (fun i=>w (i,false)&&w (i,true))

def a3Weight (x : I→Bool) (z : I→Bool×Bool) : K :=
  ∏ i, lag (z i).1 (-bit (x i))*lag (z i).2 (-1)

theorem a3_one_coordinate (x b : Bool) :
    (∑ z : Bool×Bool,(a3Tag (K:=K) (z.1&&z.2) b * lag z.1 (-bit x))*lag z.2 (-1)) =
      a3Tag (K:=K) x b := by
  rw [Fintype.sum_prod_type]
  exact shifted_copy_identity (fun u=>a3Tag (K:=K) u b) x

theorem a3_target_delta (x b : I→Bool) :
    (∑ z : I→Bool×Bool,(∏ i,a3Tag (K:=K) (a3And z i) (b i))*a3Weight x z) =
      if x=b then 1 else 0 := by
  let h (i : I) (z : Bool×Bool) :=
    (a3Tag (K:=K) (z.1&&z.2) (b i)*lag z.1 (-bit (x i)))*lag z.2 (-1)
  calc
    _ = ∑ z : I→Bool×Bool,∏ i : I,h i (z i) := by
      apply Finset.sum_congr rfl
      intro z _
      unfold a3Weight
      simp only [a3And,h,Finset.prod_mul_distrib,mul_assoc]
    _ = ∏ i : I,∑ a : Bool×Bool,h i a := (Fintype.prod_sum h).symm
    _ = _ := by
      simp only [h,a3_one_coordinate]
      exact a3Tag_product x b

theorem a3_pair_tensor_exact (f : (I→Bool)→Bool) (x : I→Bool) :
    (∑ z : I→Bool×Bool,bit (K:=K) (f (a3And z))*a3Weight x z)=bit (K:=K) (f x) := by
  have splitValue (z : I→Bool×Bool) :
      bit (K:=K) (f (a3And z))=
        ∑ b : I→Bool,bit (K:=K) (f b)*∏ i,a3Tag (K:=K) (a3And z i) (b i) := by
    simp only [a3Tag_product,mul_ite,mul_one,mul_zero]
    simp only [eq_comm,Fintype.sum_ite_eq']
  calc
    _ = ∑ b : I→Bool,bit (K:=K) (f b)*
        (∑ z : I→Bool×Bool,(∏ i,a3Tag (K:=K) (a3And z i) (b i))*a3Weight x z) := by
      simp_rw [splitValue,Finset.sum_mul,mul_assoc]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp only [a3_target_delta,mul_ite,mul_one,mul_zero]
      rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _)]
      · rw [if_pos rfl]
      · intro b _ hb
        exact if_neg (Ne.symm hb)

theorem a3_actual_two_ports_per_coordinate (f : (I→Bool)→Bool) (x : I→Bool) :
    (∑ w : (I×Bool)→Bool,bit (K:=K) (a3Table f w)*
      ∏ p : I×Bool,lag (w p) (if p.2 then -1 else -bit (x p.1)))=bit (K:=K) (f x) := by
  refine (Fintype.sum_equiv (a3PairCube (I:=I)) _ _ (fun w=>?_)).trans (a3_pair_tensor_exact f x)
  have h : (∏ p : I×Bool, lag (w p) (if p.2 then (-1:K) else -bit (x p.1))) =
      a3Weight x (a3PairCube w) := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fintype.prod_bool]
    exact mul_comm _ _
  rw [h]
  rfl

theorem a3_row_card (d : ℕ) : Fintype.card (Fin d×Bool)=2*d := by
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,mul_comm]

#print axioms a3_one_coordinate
#print axioms a3_target_delta
#print axioms a3_pair_tensor_exact
#print axioms a3_actual_two_ports_per_coordinate
#print axioms a3_row_card
end
end A2R45Literal
