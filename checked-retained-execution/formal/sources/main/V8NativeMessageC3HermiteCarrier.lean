import V8NativeMessageC3HermiteLocal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

/-! The exact signed binomial value of the printed MAIN origin carrier.
Finite ranges include both endpoints, and the erased node is positive. -/
namespace V8NativeMessage.C3.Hermite
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6ActiveHermite
noncomputable section

def leftNodes (v : ℕ) : Finset ℕ := Finset.Icc 1 (v-1)
def rightNodes (Q v : ℕ) : Finset ℕ := Finset.Icc (v+1) Q

theorem split_nodes {Q v : ℕ} (hv : v∈nodes Q) :
    (nodes Q).erase v=leftNodes v ∪ rightNodes Q v := by
  have h := Finset.mem_Icc.mp hv
  ext w
  simp only [nodes,leftNodes,rightNodes,Finset.mem_erase,Finset.mem_union,Finset.mem_Icc]
  omega

theorem disjoint_nodes (Q v : ℕ) : Disjoint (leftNodes v) (rightNodes Q v) := by
  apply Finset.disjoint_left.mpr
  intro w h h'
  have h₁ := (Finset.mem_Icc.mp h).2
  have h₂ := (Finset.mem_Icc.mp h').1
  omega

theorem interval_shift_product {A : Type*} [CommMonoid A] (a n : ℕ) (f : ℕ→A) :
    (∏ w∈Finset.Icc (a+1) (a+n),f w) = ∏ j∈Finset.range n, f (a+j+1) := by
  symm
  refine Finset.prod_bij (fun j _ => a+j+1) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    change a+j+1 ∈ Finset.Icc (a+1) (a+n)
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro j hj k hk h
    change a+j+1=a+k+1 at h
    omega
  · intro w hw
    have h := Finset.mem_Icc.mp hw
    refine ⟨w-(a+1),Finset.mem_range.mpr (by omega),?_⟩
    change a+(w-(a+1))+1=w
    omega
  · intro j _
    rfl

theorem positive_product (n : ℕ) :
    (∏ w∈Finset.Icc 1 n,(w:ℚ)) = (n.factorial:ℚ) := by
  rw [← show 0+n=n by omega]
  rw [interval_shift_product 0 n]
  rw [Nat.zero_add, Nat.factorial_eq_prod_range_add_one]
  simp only [Nat.zero_add,Nat.cast_prod]

theorem left_diff_product (v : ℕ) :
    (∏ w∈leftNodes v,((v:ℚ)-(w:ℚ))) = ∏ w∈leftNodes v,(w:ℚ) := by
  refine Finset.prod_bij (fun w _ => v-w) ?_ ?_ ?_ ?_
  · intro w hw
    have h := Finset.mem_Icc.mp hw
    change v-w ∈ Finset.Icc 1 (v-1)
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro w hw u hu h
    have hp := Finset.mem_Icc.mp hw
    have hq := Finset.mem_Icc.mp hu
    change v-w=v-u at h
    omega
  · intro w hw
    have h := Finset.mem_Icc.mp hw
    refine ⟨v-w,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    change v-(v-w)=w
    omega
  · intro w hw
    have h := Finset.mem_Icc.mp hw
    rw [Nat.cast_sub (show w≤v by omega)]

theorem left_ratio_product (v : ℕ) :
    (∏ w∈leftNodes v, (-(w:ℚ))/((v:ℚ)-(w:ℚ)))=(-1:ℚ)^(v-1) := by
  have hleft : (leftNodes v).card=v-1 := by
    simp [leftNodes,Nat.card_Icc]
  have hne : (∏ w∈leftNodes v,(w:ℚ))≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw
    have h := (Finset.mem_Icc.mp hw).1
    exact_mod_cast Nat.ne_of_gt (show 0<w by omega)
  have sc (w : ℕ) : (-(w:ℚ))/((v:ℚ)-(w:ℚ)) =
      (-1:ℚ)*((w:ℚ)/((v:ℚ)-(w:ℚ))) := by rw [← mul_div_assoc]; ring
  simp only [sc,Finset.prod_mul_distrib,Finset.prod_const]
  rw [hleft,Finset.prod_div_distrib,left_diff_product,div_self hne,mul_one]

theorem lower_upper_partition {Q v : ℕ} (hv : v≤Q) :
    Finset.Icc 1 Q = Finset.Icc 1 v ∪ rightNodes Q v := by
  ext w
  simp only [Finset.mem_Icc,Finset.mem_union,rightNodes]
  omega

theorem right_diff_factorial {Q v : ℕ} (hv : v≤Q) :
    (∏ w∈rightNodes Q v,((w:ℚ)-(v:ℚ)))=((Q-v).factorial:ℚ) := by
  unfold rightNodes
  conv_lhs => rw [← Nat.add_sub_of_le hv, interval_shift_product v (Q-v)]
  simp only [Nat.cast_add, Nat.cast_one]
  have hs (j : ℕ) : (v:ℚ)+(j:ℚ)+1-v=(j:ℚ)+1 := by ring
  simp only [hs]
  rw [Nat.factorial_eq_prod_range_add_one,Nat.cast_prod]
  simp only [Nat.cast_add,Nat.cast_one]

theorem right_ratio_product {Q v : ℕ} (hv : v≤Q) :
    (∏ w∈rightNodes Q v, (-(w:ℚ))/((v:ℚ)-(w:ℚ)))=(Q.choose v:ℚ) := by
  have dis : Disjoint (Finset.Icc 1 v) (rightNodes Q v) := by
    apply Finset.disjoint_left.mpr
    intro w hw h'
    have ha := (Finset.mem_Icc.mp hw).2
    have hb := (Finset.mem_Icc.mp h').1
    omega
  have whole : (v.factorial:ℚ)*(∏ w∈rightNodes Q v,(w:ℚ))=(Q.factorial:ℚ) := by
    rw [← positive_product v,← Finset.prod_union dis,← lower_upper_partition hv,positive_product]
  have ht (w : ℕ) : (-(w:ℚ))/((v:ℚ)-(w:ℚ))=(w:ℚ)/((w:ℚ)-(v:ℚ)) := by
    rw [show (v:ℚ)-(w:ℚ)=-((w:ℚ)-(v:ℚ)) by ring,neg_div_neg_eq]
  simp only [ht,Finset.prod_div_distrib,right_diff_factorial hv]
  apply (div_eq_iff (by positivity : ((Q-v).factorial:ℚ)≠0)).mpr
  apply mul_left_cancel₀ (by positivity : (v.factorial:ℚ)≠0)
  rw [whole,← mul_assoc,mul_comm (v.factorial:ℚ)]
  exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hv).symm

theorem origin_carrier_exact {Q v : ℕ} (J : ℕ) (hv : v∈nodes Q) :
    (carrier Q J v).eval 0 = (((-1:ℚ)^(v-1))*(Q.choose v:ℚ))^J := by
  have hu := (Finset.mem_Icc.mp hv).2
  unfold carrier normalizer
  simp only [eval_prod,eval_pow,eval_mul,eval_C,eval_sub,eval_X,zero_sub]
  rw [Finset.prod_pow]
  congr 1
  have he (w : ℕ) : invDiff v w*(-(w:ℚ)) = (-(w:ℚ))/((v:ℚ)-(w:ℚ)) := by
    rw [invDiff,div_eq_mul_inv,mul_comm]
  simp only [he]
  rw [split_nodes hv,Finset.prod_union (disjoint_nodes Q v),left_ratio_product,right_ratio_product hu]

theorem origin_carrier_integral {Q v : ℕ} (J : ℕ) (hv : v∈nodes Q) :
    (carrier Q J v).eval 0 ∈ twoLocalSubalgebra := by
  rw [origin_carrier_exact J hv]
  apply (mem_twoLocal_iff _).mpr
  refine ⟨(((-1:ℤ)^(v-1))*(Q.choose v:ℤ))^J,1,by decide,?_⟩
  simp only [Int.cast_one,div_one,Int.cast_pow,Int.cast_mul,Int.cast_neg,Int.cast_natCast]

#print axioms split_nodes
#print axioms interval_shift_product
#print axioms left_diff_product
#print axioms left_ratio_product
#print axioms right_diff_factorial
#print axioms right_ratio_product
#print axioms origin_carrier_exact
#print axioms origin_carrier_integral
end
end V8NativeMessage.C3.Hermite