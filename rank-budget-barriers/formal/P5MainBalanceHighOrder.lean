import P5MainIteratorScheduledUpper
import P5MainBalanceOrderCap

/-! Finite high-order extraction and the low-order entropy comparison
specific to (M.6). The measurement budget must be supplied for the actual
source rows, not from the coarse τ upper used for all execution costs. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Real

theorem high_order_after_low_exclusion {A : Type*} [Fintype A]
    (order rank : A→ℕ) (d q₀ : ℕ)
    (hSum : 2^d≤∑ a,rank a)
    (hcard : Fintype.card A<2^(d-d/2))
    (hsmall : ∀ a,order a≤q₀ → rank a≤2^(d/2)) :
    ∃ a,q₀<order a ∧ 2^(d/2)<rank a := by
  by_contra! h
  have hg (a : A) : rank a≤2^(d/2) := by
    by_cases ha : order a≤q₀
    · exact hsmall a ha
    · exact h a (lt_of_not_ge ha)
  have H : (∑ a,rank a)≤Fintype.card A*2^(d/2) := by
    calc
      _ ≤ ∑ _a : A,2^(d/2) := Finset.sum_le_sum (fun a _=>hg a)
      _ = _ := by simp
  have hd : d-d/2+d/2=d := Nat.sub_add_cancel (Nat.div_le_self _ _)
  have hlt : Fintype.card A*2^(d/2) < 2^d := by
    rw [←hd,pow_add,hd]
    exact Nat.mul_lt_mul_of_pos_right hcard (Nat.pow_pos (by decide))
  omega

theorem taylor_small_window_budget {W : Type*} [Fintype W] [DecidableEq W]
    (j Q N a : ℕ) (ε : ℝ)
    (hQ : 2≤Q) (_hN : 0<N) (_he : 0≤ε)
    (hvars : Fintype.card W≤a*N)
    (hfast : 2*(a:ℝ)≤ε*sqrt (Q:ℝ))
    (hOrder : (j:ℝ)*log (2*(Q:ℝ))≤ε*(N:ℝ)/sqrt (Q:ℝ)) :
    ((P5MainIterator.TaylorList W j).card:ℝ) ≤
      exp (2*ε*(N:ℝ)/sqrt (Q:ℝ)) := by
  have hQ' : 0<(Q:ℝ) := by exact_mod_cast (by omega : 0<Q)
  have hQ1 : 1≤(Q:ℝ) := by exact_mod_cast (by omega : 1≤Q)
  have hs : 0<sqrt (Q:ℝ) := sqrt_pos.2 hQ'
  let x := 1/(Q:ℝ)
  have hx : 0<x := by dsimp [x]; positivity
  have hx1 : x≤1 := by dsimp [x]; exact (div_le_iff₀ hQ').mpr (by simpa using hQ1)
  have HT := P5MainIterator.taylor_list_upper_at (V:=W) j x hx hx1
  have hd := (le_div_iff₀ (pow_pos hx j)).mpr HT
  apply hd.trans
  have hw : x^j=exp (-(j:ℝ)*log (Q:ℝ)) := by
    have hpow : exp ((j:ℝ)*log (Q:ℝ))=(Q:ℝ)^j := by rw [exp_nat_mul,exp_log hQ']
    rw [neg_mul,exp_neg,hpow]
    dsimp [x]
    rw [one_div,inv_pow]
  rw [hw,←exp_sub]
  apply exp_le_exp.mpr
  have hn : (Fintype.card W:ℝ)≤(a:ℝ)*(N:ℝ) := by exact_mod_cast hvars
  have hᵤ : 2*x*(Fintype.card W:ℝ)≤ε*(N:ℝ)/sqrt (Q:ℝ) := by
    have H := mul_le_mul_of_nonneg_right hfast (show 0≤(N:ℝ) by positivity)
    dsimp [x]
    calc
      _ ≤ 2*(1/(Q:ℝ))*((a:ℝ)*(N:ℝ)) := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = (2*(a:ℝ)*(N:ℝ))/(Q:ℝ) := by ring
      _ ≤ (ε*sqrt (Q:ℝ)*(N:ℝ))/(Q:ℝ) := div_le_div_of_nonneg_right (by simpa only [mul_assoc] using H) hQ'.le
      _ = _ := by
        have H : sqrt (Q:ℝ)/(Q:ℝ)=1/sqrt (Q:ℝ) := by
          apply (div_eq_div_iff hQ'.ne' hs.ne').mpr
          rw [←pow_two,sq_sqrt hQ'.le,one_mul]
        rw [show (ε*sqrt (Q:ℝ)*(N:ℝ))/(Q:ℝ)=(ε*(N:ℝ))*(sqrt (Q:ℝ)/(Q:ℝ)) by ring,H]
        ring
  have hLog : log (Q:ℝ)≤log (2*(Q:ℝ)) :=
    log_le_log hQ' (by linarith only [hQ'])
  have hⱼ := (mul_le_mul_of_nonneg_left hLog (show 0≤(j:ℝ) by positivity)).trans hOrder
  rw [neg_mul,sub_neg_eq_add]
  calc
    _ ≤ ε*(N:ℝ)/sqrt (Q:ℝ)+ε*(N:ℝ)/sqrt (Q:ℝ) := add_le_add hᵤ hⱼ
    _ = _ := by ring

theorem combining_low_costs {W : Type*} [Fintype W] [DecidableEq W]
    (j Q N a Y ell : ℕ) (ε : ℝ)
    (hQ : 2≤Q) (_hN : 0<N) (_he : 0≤ε)
    (hvars : Fintype.card W≤a*N)
    (hfast : 2*(a:ℝ)≤ε*sqrt (Q:ℝ))
    (hOrder : (j:ℝ)*log (2*(Q:ℝ))≤ε*(N:ℝ)/sqrt (Q:ℝ))
    (hSmall : ((Y*ell*(j+1):ℕ):ℝ)≤exp (ε*(N:ℝ)/sqrt (Q:ℝ))) :
    (((P5MainIterator.TaylorList W j).card * Y * (ell*(j+1)):ℕ):ℝ)≤
      exp (3*ε*(N:ℝ)/sqrt (Q:ℝ)) := by
  have h := taylor_small_window_budget (W:=W) j Q N a ε hQ _hN _he hvars hfast hOrder
  have H := mul_le_mul h hSmall (by positivity) (exp_nonneg _)
  rw [←exp_add] at H
  convert H using 1 <;> push_cast <;> ring

#print axioms high_order_after_low_exclusion
#print axioms taylor_small_window_budget
#print axioms combining_low_costs
end P5MainBalance
