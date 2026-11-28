import J4R43LiteralOutsideUnitRun

/-! Feasible scalar preprocessing for the original signed grid;
no valuation, divisibility, or exact quotient oracle is an instruction.
The two genuine derivatives share the counted trailing powers of 2. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9PacketCoeff P1DyadicGrid P1DyadicGridBridge
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5400000

structure StripRun where
  numerator : ℤ
  denominator : ℤ
  shifts : ℕ
  tests : ℕ

def stripBoth (n d : ℤ) : ℕ→StripRun
  | 0 => ⟨n,d,0,0⟩
  | k+1 =>
    if d%2=0 then
      let s := stripBoth (n/2) (d/2) k
      ⟨s.numerator,s.denominator,s.shifts+2,s.tests+1⟩
    else ⟨n,d,0,1⟩

theorem stripBoth_cap (n d : ℤ) (fuel : ℕ) :
    (stripBoth n d fuel).shifts≤2*fuel ∧ (stripBoth n d fuel).tests≤fuel := by
  induction fuel generalizing n d with
  | zero => simp [stripBoth]
  | succ fuel ih =>
    by_cases e : d%2=0
    · obtain ⟨h,k⟩ := ih (n/2) (d/2)
      simp only [stripBoth,if_pos e]
      omega
    · simp only [stripBoth,if_neg e]
      omega

theorem stripBoth_exact (s r : ℤ) (odd : Odd r) (k fuel : ℕ) (h : k≤fuel) :
    (stripBoth (pow₂ k*s) (pow₂ k*r) fuel).numerator=s ∧
    (stripBoth (pow₂ k*s) (pow₂ k*r) fuel).denominator=r := by
  induction fuel generalizing k with
  | zero =>
    have hk : k=0 := by omega
    subst k
    simp [stripBoth,pow₂]
  | succ fuel ih =>
    cases k with
    | zero =>
      have ho : r%2≠0 := by
        intro h0
        exact (Int.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr (Int.dvd_iff_emod_eq_zero.mpr h0))
      simp [stripBoth,pow₂,ho]
    | succ k =>
      have c (x : ℤ) : pow₂ (k+1)*x=2*(pow₂ k*x) := by
        simp only [pow₂,pow_succ]; ring
      have e : (pow₂ (k+1)*r)%2=0 := by rw [c]; omega
      have q (x : ℤ) : (pow₂ (k+1)*x)/2=pow₂ k*x := by rw [c]; omega
      simp only [stripBoth,if_pos e,q]
      exact ih k (by omega)

def derivativeWidth (a : ℕ) : ℕ := (a+1)*(2*2^a-1)

def paidNormalizeUnit (a : ℕ) (t : ℤ) : StripRun :=
  stripBoth (derivativeTape a t).prod (derivativeTape a 0).prod (derivativeWidth a)

theorem normalized_unit_is_original (a : ℕ) {t : ℤ} (mem : t∈grid a) :
    let out := paidNormalizeUnit a t
    out.numerator=scaledDerivative a t ∧ out.denominator=scaledDerivative a 0 ∧
      out.shifts≤2*derivativeWidth a ∧ out.tests≤derivativeWidth a := by
  let T := (cauchyPolynomial a).derivative.eval t
  let Z := (cauchyPolynomial a).derivative.eval 0
  obtain ⟨k,s,r,_,odd,ht,hz⟩ := cauchy_derivative_common_content mem
  have nu : padicValInt 2 Z=k := by
    change padicValInt 2 ((cauchyPolynomial a).derivative.eval 0)=k
    rw [hz,valuation_pow₂_mul_odd k odd]
  have cap : k≤derivativeWidth a := nu ▸ source_zero_valuation_fits a
  have div (x : ℤ) : (pow₂ k*x)/pow₂ k=x := by
    rw [mul_comm]
    exact Int.mul_ediv_cancel x (ne_of_gt (pow₂_pos k))
  have nn : scaledDerivative a t=s := by
    unfold scaledDerivative
    rw [←cauchy_derivative_eval (zero_mem_grid a),←cauchy_derivative_eval mem,nu,ht,div]
  have dd : scaledDerivative a 0=r := by
    unfold scaledDerivative
    rw [←cauchy_derivative_eval (zero_mem_grid a),nu,hz,div]
  have c := stripBoth_cap T Z (derivativeWidth a)
  have d := stripBoth_exact s r odd k (derivativeWidth a) cap
  change T=pow₂ k*s at ht
  change Z=pow₂ k*r at hz
  rw [←ht,←hz] at d
  simp only [paidNormalizeUnit,derivativeTape_exact mem,derivativeTape_exact (zero_mem_grid a),nn,dd]
  exact ⟨d.1,d.2,c.1,c.2⟩

/-- The outer two derivative products use this exact many grid gaps,
before the separately charged odd reconstruction. -/
theorem raw_derivative_visits (a : ℕ) {t : ℤ} (mem : t∈grid a) :
    (derivativeTape a t).length+(derivativeTape a 0).length=2*(2*2^a-1) := by
  rw [derivativeTape_count a mem,derivativeTape_count a (zero_mem_grid a)]
  omega

variable {R : Type} [CommRing R]

def paidSourceUnit (a : ℕ) (t : ℤ) (p : ℕ) : R×ℕ :=
  let q := paidNormalizeUnit a t
  let z : R := -((2:R)*((q.denominator/2:ℤ):R))
  let out := geoRun z p
  ((q.numerator:R)*out.1,out.2+3)

theorem actual_paid_source_unit (a : ℕ) {t : ℤ} (mem : t∈grid a)
    (p : ℕ) (nil : (2:R)^p=0) :
    let z := paidSourceUnit (R:=R) a t p
    z.1=J6ZeroTransport.reduceAt p nil (rho a t) ∧ z.2=2*p+3 := by
  obtain ⟨nr,dr,_,_⟩ := normalized_unit_is_original a mem
  dsimp only [paidSourceUnit]
  rw [nr,dr]
  exact actual_unit_run a mem p nil

#print axioms stripBoth_cap
#print axioms stripBoth_exact
#print axioms normalized_unit_is_original
#print axioms raw_derivative_visits
#print axioms actual_paid_source_unit
end
end J4R43LiteralOutside

