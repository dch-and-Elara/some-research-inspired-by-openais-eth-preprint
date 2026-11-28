import P5MainBalanceM6SizeB
import P5MainBalanceHermite

/-! The exact printed J=floor(dR/Q)+1 and retained coefficient address
count. This closes the polynomial-size hypothesis at fixed density
rather than asking the caller to certify asymptotics of the schedule. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Real Filter
open scoped BigOperators Classical

noncomputable def printedOrder (n d : ℕ) : ℕ := d*mainWidth 1 n/mainNodes n+1

theorem source_nominal_grid_bound (n d : ℕ) :
    mainNodes n*printedOrder n d ≤ d*mainWidth 1 n+mainNodes n := by
  unfold printedOrder
  rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm (mainNodes n) (d*mainWidth 1 n/mainNodes n)]
  exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

theorem mainWidth_le_four_lambda (n : ℕ) : mainWidth 1 n ≤ 4*mainLambda n := by
  unfold mainWidth
  apply Nat.mul_le_mul_left 4
  apply Nat.ceil_le.mpr
  by_cases h : mainLambda n=0
  · simp [h]
  · have h₁ : (1:ℝ)≤mainLambda n := by exact_mod_cast (by omega : 1≤mainLambda n)
    have hn : 0≤(mainLambda n:ℝ) := by positivity
    have hc : (mainLambda n:ℝ)≤(mainLambda n:ℝ)^2 := by
      simpa only [mul_one,pow_two] using mul_le_mul_of_nonneg_left h₁ hn
    have hh := sqrt_le_sqrt hc
    rwa [sqrt_sq hn] at hh

theorem printed_width_nodes_at_most_n :
    ∀ᶠ n : ℕ in atTop, mainWidth 1 n≤n ∧ mainNodes n≤n := by
  let K := 4*logEightBound+2
  have hK2 : 2≤K := by
    dsimp [K,logEightBound]
    linarith only [show 0≤8/log 2 by positivity]
  have hK1 : 1≤K := by linarith only [hK2]
  have hT := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (K^8))
  filter_upwards [hT] with n hn
  let z := eighth (n:ℝ)
  have hzK : K≤z := by
    rw [←eighth_pow_inverse K (by linarith only [hK2])]
    exact eighth_mono hn
  have hz : 1≤z := hK1.trans hzK
  have hn1 : 1≤(n:ℝ) := (one_le_pow₀ hK1).trans hn
  have h : 4*(mainLambda n:ℝ)≤(n:ℝ) := by
    calc
      _ ≤ 4*(logEightBound*z) :=
        mul_le_mul_of_nonneg_left (ceil_logTwo_le _ hn1) (by norm_num)
      _ ≤ z*z := by
        have h₀ : 4*logEightBound≤z := by dsimp [K] at hzK; linarith only [hzK]
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right h₀ (by linarith only [hz])
      _ = z^2 := by ring
      _ ≤ z^8 := pow_le_pow_right₀ hz (by decide)
      _ = _ := eighth_pow _ (by positivity)
  have hN : 4*mainLambda n≤n := by exact_mod_cast h
  exact ⟨(mainWidth_le_four_lambda n).trans hN,
    (Nat.div_le_self _ _).trans (by omega)⟩

theorem sparse_nominal_grade_linear (k m ell n c : ℕ) (hm : m≤c*n) (hl : ell≤n+1) :
    k*(m+2*(ell-1))≤(k*(c+2))*n := by
  rw [Nat.mul_assoc,Nat.add_mul]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add hm (Nat.mul_le_mul_left _ (by omega)))

set_option maxHeartbeats 4600000 in
theorem eventual_printed_address_count (b : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ d ell : ℕ,d≤b*n → ell≤n+1 →
      Fintype.card (JetIndex (fun _ : Fin (mainNodes n)=>printedOrder n d) × Fin ell) ≤ n^5 := by
  filter_upwards [eventually_ge_atTop (max 2 (b+1)),printed_width_nodes_at_most_n] with n hn hW
  intro d ell hd he
  have hn2 : 2≤n := (le_max_left _ _).trans hn
  have hnb : b+1≤n := (le_max_right _ _).trans hn
  have hCount : Fintype.card (JetIndex (fun _ : Fin (mainNodes n)=>printedOrder n d) × Fin ell) =
      (mainNodes n*printedOrder n d)*ell := by
    rw [Fintype.card_prod,Fintype.card_sigma]
    simp
  rw [hCount]
  have hN2 : n≤n*n := by nlinarith only [hn2]
  have hP : mainNodes n*printedOrder n d≤n^3 := by
    calc
      _ ≤ d*mainWidth 1 n+mainNodes n := source_nominal_grid_bound _ _
      _ ≤ (b*n)*n+n*n :=
        Nat.add_le_add (Nat.mul_le_mul hd hW.1) (hW.2.trans hN2)
      _ = (b+1)*(n*n) := by ring
      _ ≤ n*(n*n) := Nat.mul_le_mul_right _ hnb
      _ = _ := by ring
  have hE : ell≤n^2 := he.trans (by nlinarith only [hn2])
  exact (Nat.mul_le_mul hP hE).trans_eq (by ring)

#print axioms source_nominal_grid_bound
#print axioms mainWidth_le_four_lambda
#print axioms printed_width_nodes_at_most_n
#print axioms sparse_nominal_grade_linear
#print axioms eventual_printed_address_count
end P5MainBalance.M6
