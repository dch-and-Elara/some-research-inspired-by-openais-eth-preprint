import J4R43LiteralOutsideRawMagnitude
import J4R43LiteralOutsideBitStrip
import J4R43LiteralOutsideUnitSeedWords

/-! Same literal derivative normalization, now from the bit-valued
magnitude products and a single scan of their low bits. The two
generated p-bit words have the original signed meaning. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid P1DyadicGridBridge DenominatorBudget J6R9PacketCoeff
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7400000
set_option Elab.async false

theorem signed_magnitude_means_int (d : ℤ) (b : Bool) (x : List Bool)
    (sign : b=decide (d<0)) (mag : bitsValue x=d.natAbs) :
    signedDenote b x=d := by
  unfold signedDenote
  rw [sign,mag]
  by_cases neg : d<0
  · rw [decide_eq_true neg]
    change -(d.natAbs:ℤ)=d
    have e := Int.natAbs_of_nonneg (show 0≤-d by omega)
    rw [Int.natAbs_neg] at e
    omega
  · rw [decide_eq_false neg]
    change (d.natAbs:ℤ)=d
    exact Int.natAbs_of_nonneg (by omega)

theorem odd_absolute_has_low_bit {d : ℤ} (odd : Odd d) : d.natAbs%2=1 := by
  have h : ((d.natAbs:ℤ)%2)=1 := by
    by_cases neg : d<0
    · have e := Int.natAbs_of_nonneg (show 0≤-d by omega)
      rw [Int.natAbs_neg] at e
      obtain ⟨j,hj⟩ := odd
      omega
    · rw [Int.natAbs_of_nonneg (by omega)]
      obtain ⟨j,hj⟩ := odd
      omega
  exact_mod_cast h

def nativeWordNormalize (p : ℕ) (hp : 0<p) (a : ℕ) (t : ℤ) :
    Meter (Word p×Word p) :=
  let M := derivativeMagnitudeRun a t
  let D := derivativeMagnitudeRun a 0
  let B := stripMagnitudeBits M.result.val D.result.val (derivativeWidth a)
  let S := orderedDerivative a t
  let Q := orderedDerivative a 0
  let n := signedWord hp (negativeParity S) B.numerator
  let d := signedWord hp (negativeParity Q) B.denominator
  ⟨(n.result,d.result), M.steps+D.steps+B.steps+n.steps+d.steps+2*(S.length+Q.length)⟩

def nativeWordNormalizeFee (a p : ℕ) :=
  let w := derivativeWidth a+1
  let n := 2*2^a-1
  2*(3*w+3+n*(wordOpCap w+6*w+8))+(4*derivativeWidth a+2)+(38*p+12)+4*n

theorem actual_native_word_normalize (p : ℕ) (hp : 0<p) (a : ℕ) {t : ℤ} (mem : t∈grid a) :
    let run := nativeWordNormalize p hp a t
    let q := paidNormalizeUnit a t
    wordRead run.result.1=(q.numerator:NativeProbeRing.Base p) ∧
    wordRead run.result.2=(q.denominator:NativeProbeRing.Base p) ∧
      run.steps≤nativeWordNormalizeFee a p := by
  let S := orderedDerivative a t
  let Q := orderedDerivative a 0
  let M := derivativeMagnitudeRun a t
  let D := derivativeMagnitudeRun a 0
  let B := stripMagnitudeBits M.result.val D.result.val (derivativeWidth a)
  let n := signedWord hp (negativeParity S) B.numerator
  let d := signedWord hp (negativeParity Q) B.denominator
  obtain ⟨k,s,r,_,odd,x,y⟩ := cauchy_derivative_common_content mem
  have ht : S.prod=pow₂ k*s :=
    ((ordered_derivative_actual a (t:=t)).trans (derivativeTape_exact mem)).trans x
  have h0 : Q.prod=pow₂ k*r :=
    ((ordered_derivative_actual a (t:=0)).trans (derivativeTape_exact (zero_mem_grid a))).trans y
  have q : paidNormalizeUnit a t=explicitNormalizeUnit a t :=
    (explicit_normalize_is_native a mem).symm
  have bound : k≤derivativeWidth a := by
    have v := source_zero_valuation_fits a
    rwa [y,valuation_pow₂_mul_odd k odd] at v
  have atN := actual_grid_magnitude_receipt a mem
  have atD := actual_grid_magnitude_receipt a (zero_mem_grid a)
  have Rn : bitsValue M.result.val=2^k*s.natAbs := by
    have x₀ : bitsValue M.result.val=S.prod.natAbs := atN.1
    rw [x₀,ht,Int.natAbs_mul]
    simp [pow₂,Int.natAbs_pow]
  have Rd : bitsValue D.result.val=2^k*r.natAbs := by
    have y₀ : bitsValue D.result.val=Q.prod.natAbs := atD.1
    rw [y₀,h0,Int.natAbs_mul]
    simp [pow₂,Int.natAbs_pow]
  have bitsOut := common_binary_stripping_exact M.result.val D.result.val s.natAbs r.natAbs
    (odd_absolute_has_low_bit odd) k (derivativeWidth a) Rn Rd bound
  have signN : negativeParity S=decide (s<0) := by
    have n₀ : negativeParity S=decide (S.prod<0) := atN.2.2
    rw [n₀,ht]
    simp [mul_neg_iff,(pow₂_pos k),not_lt_of_ge (pow₂_pos k).le]
  have signD : negativeParity Q=decide (r<0) := by
    have d₀ : negativeParity Q=decide (Q.prod<0) := atD.2.2
    rw [d₀,h0]
    simp [mul_neg_iff,(pow₂_pos k),not_lt_of_ge (pow₂_pos k).le]
  have norm := stripBoth_exact s r odd k (derivativeWidth a) bound
  have E : (paidNormalizeUnit a t).numerator=s ∧ (paidNormalizeUnit a t).denominator=r := by
    rw [q]
    unfold explicitNormalizeUnit
    change (stripBoth S.prod Q.prod (derivativeWidth a)).numerator=s ∧ _
    rw [ht,h0]
    exact norm
  obtain ⟨nr,nf⟩ := signedWord_exact hp (negativeParity S) B.numerator
  obtain ⟨dr,df⟩ := signedWord_exact hp (negativeParity Q) B.denominator
  have vf := strip_bits_fee M.result.val D.result.val (derivativeWidth a)
  have Sl := ordered_derivative_len a mem
  have Ql := ordered_derivative_len a (zero_mem_grid a)
  dsimp only
  refine ⟨?_,?_,?_⟩
  · change wordRead n.result=((paidNormalizeUnit a t).numerator:NativeProbeRing.Base p)
    rw [nr,signed_magnitude_means_int s _ _ signN bitsOut.1,E.1]
  · change wordRead d.result=((paidNormalizeUnit a t).denominator:NativeProbeRing.Base p)
    rw [dr,signed_magnitude_means_int r _ _ signD bitsOut.2,E.2]
  · change M.steps+D.steps+B.steps+n.steps+d.steps+2*(S.length+Q.length)≤_
    change n.steps≤_ at nf
    change d.steps≤_ at df
    change B.steps≤_ at vf
    have mn := atN.2.1
    have md := atD.2.1
    change M.steps≤_ at mn
    change D.steps≤_ at md
    change S.length=_ at Sl
    change Q.length=_ at Ql
    rw [Sl,Ql]
    dsimp only [nativeWordNormalizeFee]
    omega

#print axioms signed_magnitude_means_int
#print axioms odd_absolute_has_low_bit
#print axioms actual_native_word_normalize
end
end J4R43LiteralOutside

