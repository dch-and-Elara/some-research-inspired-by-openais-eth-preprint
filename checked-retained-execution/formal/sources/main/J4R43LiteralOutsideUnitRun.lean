import J4R43LiteralOutsideUnit

/-! Explicit arithmetic schedule for the actual unit at any active
signed centre. Its odd inverse is Horner multiplication and addition,
not an uncharged ring-inverse instruction. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9PacketCoeff P1DyadicGrid P1DyadicGridBridge
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4200000

def derivativeTape (a : ℕ) (t : ℤ) : List ℤ :=
  ((grid a).erase t).toList.map (fun q=>t-q)

theorem derivativeTape_exact {a : ℕ} {t : ℤ} (h : t∈grid a) :
    (derivativeTape a t).prod=(cauchyPolynomial a).derivative.eval t := by
  rw [cauchy_derivative_eval h,derivativeTape,Finset.prod_map_toList]

theorem derivativeTape_count (a : ℕ) {t : ℤ} (h : t∈grid a) :
    (derivativeTape a t).length=2*2^a-1 := by
  rw [derivativeTape,List.length_map,Finset.length_toList,Finset.card_erase_of_mem h]
  have hcard : (grid a).card=2*2^a := by
    rw [actual_grid_as_printed,J8Physical.printedGrid,Int.card_Ico]
    omega
  rw [hcard]

theorem source_zero_valuation_fits (a : ℕ) :
    padicValInt 2 ((cauchyPolynomial a).derivative.eval 0)≤(a+1)*(2*2^a-1) := by
  let x := (cauchyPolynomial a).derivative.eval 0
  let n := padicValInt 2 x
  have upper := derivative_input_width a (zero_mem_grid a)
  obtain ⟨d,odd,hd⟩ := integer_odd_factor (cauchy_derivative_nonzero (zero_mem_grid a))
  have pd : (1:ℤ)≤|d| := by
    have h := odd_int_ne_zero odd
    exact Int.one_le_abs h
  have lo : (2:ℤ)^n≤|x| := by
    change x=pow₂ n*d at hd
    rw [hd,abs_mul,abs_of_nonneg (pow₂_pos n).le,pow₂]
    exact le_mul_of_one_le_right (by positivity) pd
  change n≤_
  by_contra! big
  have h := pow_lt_pow_right₀ (by decide : (1:ℤ)<2) big
  exact (not_lt_of_ge (lo.trans upper) h)

variable {R : Type} [CommRing R]

def geoRun (x : R) : ℕ→R×ℕ
  | 0 => (0,0)
  | p+1 =>
    let out := geoRun x p
    (1+x*out.1,2+out.2)

theorem geoRun_correct (x : R) (p : ℕ) :
    (geoRun x p).1=∑ j∈Finset.range p,x^j := by
  induction p with
  | zero => simp [geoRun]
  | succ p ih =>
    simp only [geoRun,ih]
    rw [Finset.sum_range_succ',Finset.mul_sum]
    simp only [pow_succ',pow_zero]
    rw [add_comm]

theorem geoRun_fee (x : R) (p : ℕ) : (geoRun x p).2=2*p := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [geoRun,ih]; omega

def unitRun (a : ℕ) (t : ℤ) (p : ℕ) : R×ℕ :=
  let d := scaledDerivative a 0
  let z : R := -((2:R)*((d/2:ℤ):R))
  let out := geoRun z p
  ((scaledDerivative a t:R)*out.1, out.2+3)

theorem actual_unit_run (a : ℕ) {t : ℤ} (mem : t∈grid a)
    (p : ℕ) (nil : (2:R)^p=0) :
    (unitRun (R:=R) a t p).1=J6ZeroTransport.reduceAt p nil (rho a t) ∧
      (unitRun (R:=R) a t p).2=2*p+3 := by
  constructor
  · rw [unitRun,geoRun_correct,compute_actual_unit a mem p nil]
    rfl
  · simp only [unitRun,geoRun_fee]

#print axioms derivativeTape_exact
#print axioms derivativeTape_count
#print axioms source_zero_valuation_fits
#print axioms geoRun_correct
#print axioms geoRun_fee
#print axioms actual_unit_run
end
end J4R43LiteralOutside

