import J4R43LiteralOutsideUnitWord
import A1R12Words

/-! Producing both native unit words from real normalized grid
derivatives. The result depends on the actual node and not an
external callback. Width bounds apply before reduction. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid DenominatorBudget P1DyadicGridBridge
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5600000

theorem readout_normalized_part_height (a : ℕ) {t : ℤ} (mem : t∈grid a) :
    let q := paidNormalizeUnit a t
    |q.numerator|≤(2:ℤ)^derivativeWidth a ∧
    |q.denominator|≤(2:ℤ)^derivativeWidth a := by
  obtain ⟨k,s,r,_,odd,ht,hz⟩ := cauchy_derivative_common_content mem
  have cap : k≤derivativeWidth a := by
    have v := source_zero_valuation_fits a
    rwa [hz,valuation_pow₂_mul_odd k odd] at v
  have H := stripBoth_exact s r odd k (derivativeWidth a) cap
  dsimp only [paidNormalizeUnit]
  rw [derivativeTape_exact mem,derivativeTape_exact (zero_mem_grid a),ht,hz,H.1,H.2]
  have transport (x : ℤ) (d : ℕ) (h : |pow₂ k*x|≤(2:ℤ)^d) : |x|≤(2:ℤ)^d := by
    rw [abs_mul,abs_of_nonneg (pow₂_pos k).le] at h
    have one : (1:ℤ)≤pow₂ k := by have p:=pow₂_pos k; omega
    exact (le_mul_of_one_le_left (abs_nonneg _) one).trans h
  have A := derivative_input_width a mem
  have B := derivative_input_width a (zero_mem_grid a)
  rw [ht] at A
  rw [hz] at B
  exact ⟨transport s _ A,transport r _ B⟩

def signedFixedWord {p : ℕ} (hp : 0<p) (width : ℕ) (n : ℤ) :
    Meter (Word p) :=
  signedWord hp (decide (n<0)) (encodeBits width n.natAbs)

theorem signed_fixed_word_exact {p : ℕ} (hp : 0<p) (width : ℕ) (n : ℤ)
    (fit : n.natAbs<2^width) :
    wordRead (signedFixedWord hp width n).result=(n:ZMod (2^p)) ∧
      (signedFixedWord hp width n).steps≤19*p+6 := by
  obtain ⟨r,c⟩ := signedWord_exact hp (decide (n<0)) (encodeBits width n.natAbs)
  refine ⟨r.trans ?_,c⟩
  have mag : bitsValue (encodeBits width n.natAbs)=n.natAbs := by
    rw [encodeBits_mod,Nat.mod_eq_of_lt fit]
  unfold signedDenote
  rw [mag]
  congr 1
  by_cases h : n<0
  · rw [decide_eq_true h]
    change -(n.natAbs:ℤ)=n
    have A := Int.natAbs_of_nonneg (show 0≤-n by omega)
    rw [Int.natAbs_neg] at A
    omega
  · rw [decide_eq_false h]
    change (n.natAbs:ℤ)=n
    exact Int.natAbs_of_nonneg (le_of_not_gt h)

def originalNormWords (p : ℕ) (hp : 0<p) (a : ℕ) (t : ℤ) :
    Meter (Word p) × Meter (Word p) :=
  let uv := paidNormalizeUnit a t
  (signedFixedWord hp (derivativeWidth a+1) uv.numerator,
   signedFixedWord hp (derivativeWidth a+1) uv.denominator)

theorem actual_source_norm_words (p : ℕ) (hp : 0<p) (a : ℕ) {t : ℤ} (mem : t∈grid a) :
    let B := originalNormWords p hp a t
    let o := paidNormalizeUnit a t
    wordRead B.1.result=(o.numerator:ZMod (2^p)) ∧
    wordRead B.2.result=(o.denominator:ZMod (2^p)) ∧
    B.1.steps+B.2.steps≤38*p+12 := by
  let z := paidNormalizeUnit a t
  let width := derivativeWidth a
  have H := readout_normalized_part_height a mem
  have small (x : ℤ) (h : |x|≤(2:ℤ)^width) : x.natAbs<2^(width+1) := by
    have he : (x.natAbs:ℤ)=|x| := Int.natCast_natAbs x
    have T : (x.natAbs:ℤ)≤(2:ℤ)^width := he.le.trans h
    have hh : x.natAbs≤2^width := by exact_mod_cast T
    rw [pow_succ]
    have pos : 0<(2:ℕ)^width := by positivity
    omega
  have N := signed_fixed_word_exact hp (width+1) z.numerator (small _ H.1)
  have D := signed_fixed_word_exact hp (width+1) z.denominator (small _ H.2)
  refine ⟨N.1,D.1,?_⟩
  change (signedFixedWord hp (width+1) z.numerator).steps+
    (signedFixedWord hp (width+1) z.denominator).steps≤38*p+12
  have hn := N.2
  have hd := D.2
  omega

#print axioms readout_normalized_part_height
#print axioms signed_fixed_word_exact
#print axioms actual_source_norm_words
end
end J4R43LiteralOutside

