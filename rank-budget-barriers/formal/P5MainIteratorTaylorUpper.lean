import P5MainIteratorBox
import P5MainIteratorChoose
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact Taylor generating-function bound: no Stirling approximation
is required for the asymptotic upper exponent of the paid iterator. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real

set_option maxHeartbeats 5300000 in
theorem taylor_list_upper {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (hq : 0<q) (hN : q≤Fintype.card V) :
    ((TaylorList V q).card:ℝ) ≤ ((2*exp 1*(Fintype.card V:ℝ))/(q:ℝ))^q := by
  let n := Fintype.card V
  let x := (q:ℝ)/(2*(n:ℝ))
  have hqn : (q:ℝ)≤(n:ℝ) := by exact_mod_cast hN
  have hq' : 0<(q:ℝ) := by exact_mod_cast hq
  have hn' : 0<(n:ℝ) := hq'.trans_le hqn
  have hx : 0<x := by unfold x; positivity
  have hx1 : x≤1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hqn,hn']
  have hf (j : ℕ) : (2:ℝ)^j*(n.choose j:ℝ) * x^j =
      (2*x)^j*(n.choose j:ℝ) := by rw [mul_pow]; ring
  have hs : ((TaylorList V q).card:ℝ) * x^q ≤ exp (q:ℝ) := by
    rw [card_taylorList, Nat.min_eq_left hN, Nat.cast_sum,Finset.sum_mul]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    calc
      _ ≤ ∑ j∈Finset.range (q+1),(2:ℝ)^j*(n.choose j:ℝ)*x^j := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_of_le_one hx.le hx1 (by have := Finset.mem_range.mp hj; omega)
      _ ≤ ∑ j∈Finset.range (n+1),(2:ℝ)^j*(n.choose j:ℝ)*x^j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => by positivity)
      _ = ∑ j∈Finset.range (n+1),(2*x)^j*(n.choose j:ℝ) := Finset.sum_congr rfl (fun j _ => hf j)
      _ = (2*x+1)^n := by rw [add_pow]; simp
      _ ≤ (exp (2*x))^n := pow_le_pow_left₀ (by positivity) (add_one_le_exp (2*x)) _
      _ = exp (q:ℝ) := by
        rw [←exp_nat_mul]
        congr 1
        dsimp [x]
        field_simp
  calc
    _ ≤ exp (q:ℝ)/(x^q) := (le_div_iff₀ (pow_pos hx _)).mpr hs
    _ = _ := by
      rw [show exp (q:ℝ) = (exp 1)^q by rw [←exp_nat_mul]; simp,←div_pow]
      congr 1
      dsimp [x]
      field_simp
      rfl

#print axioms taylor_list_upper
end P5MainIterator
