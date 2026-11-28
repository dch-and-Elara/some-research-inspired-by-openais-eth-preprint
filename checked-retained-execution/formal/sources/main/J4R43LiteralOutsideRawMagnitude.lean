import J4R43LiteralOutsideRawGrid
import J4R43LiteralOutsideUnitWord
import J4R43LiteralOutsideBitStrip

/-! For the actual grid, compute the signed derivative product as a
bounded magnitude product and an XOR of the factor signs. Intermediate
multiplications use fixed-width schoolbook word operations. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid P1DyadicGridBridge DenominatorBudget
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5800000

def magnitudeProduct (p : ℕ) : List ℕ→Meter (Word p)
  | [] => ⟨wordOne p,3*p+3⟩
  | n::ns =>
    let acc := magnitudeProduct p ns
    let x := natWord p n
    let m := mulWord x acc.result
    ⟨m.result,acc.steps+m.steps+6*p+8⟩

theorem product_magnitude_modular (p : ℕ) (hp : 0<p) (l : List ℕ) :
    wordRead (magnitudeProduct p l).result=(l.prod:ZMod (2^p)) ∧
    (magnitudeProduct p l).steps≤3*p+3+l.length*(wordOpCap p+6*p+8) := by
  induction l with
  | nil => simpa [magnitudeProduct] using And.intro (wordOne_read p hp) (le_refl (3*p+3))
  | cons x xs ih =>
    let acc := magnitudeProduct p xs
    let m := mulWord (natWord p x) acc.result
    have mm : m.steps≤wordOpCap p := (wordOps p hp).mul_cost _ _
    have cc : acc.steps≤3*p+3+xs.length*(wordOpCap p+6*p+8) := ih.2
    constructor
    · simp only [magnitudeProduct,mulWord_read,natWord_read,ih.1,List.prod_cons,Nat.cast_mul]
    · change acc.steps+m.steps+6*p+8≤3*p+3+(xs.length+1)*(wordOpCap p+6*p+8)
      rw [Nat.succ_mul xs.length]
      omega

theorem actual_magnitude_word_value {p : ℕ} (hp : 0<p) (l : List ℕ) (fit : l.prod<2^p) :
    bitsValue (magnitudeProduct p l).result.val=l.prod := by
  let W := (magnitudeProduct p l).result
  change bitsValue W.val=l.prod
  have read := (product_magnitude_modular p hp l).1
  change wordRead W=(l.prod:ZMod (2^p)) at read
  have bound (x : List Bool) : bitsValue x<2^x.length := by
    induction x with
    | nil => decide
    | cons b bs ih =>
      cases b <;> simp only [false_low_value,true_low_value,List.length_cons,pow_succ] <;> omega
  have h := bound W.val
  rw [W.property] at h
  have H := ZMod.val_natCast_of_lt h
  change (wordRead W).val=bitsValue W.val at H
  rw [read,ZMod.val_natCast_of_lt fit] at H
  exact H.symm

theorem product_abs_is_magnitude (l : List ℤ) :
    (l.map Int.natAbs).prod=l.prod.natAbs := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.prod_cons,ih,Int.natAbs_mul]

def negativeParity : List ℤ→Bool
  | [] => false
  | x::xs => Bool.xor (decide (x<0)) (negativeParity xs)

theorem product_sign_literal (l : List ℤ) (valid : ∀ x∈l,x≠0) :
    negativeParity l=decide (l.prod<0) ∧ l.prod≠0 := by
  induction l with
  | nil => simp [negativeParity]
  | cons x xs ih =>
    have nz := valid x List.mem_cons_self
    obtain ⟨cross,m⟩ := ih (fun z hz=>valid z (List.mem_cons_of_mem _ hz))
    constructor
    · simp only [negativeParity,List.prod_cons,cross]
      by_cases hx : x<0 <;> by_cases ht : xs.prod<0 <;>
        simp [mul_neg_iff,hx,ht,show (0:ℤ)<x ↔ ¬x<0 by omega,show (0:ℤ)<xs.prod ↔ ¬xs.prod<0 by omega]
    · exact mul_ne_zero nz m

theorem nonzero_ordered_factors (a : ℕ) (t : ℤ) :
    ∀ x∈orderedDerivative a t,x≠0 := by
  intro x hx
  obtain ⟨q,h,rfl⟩ := List.mem_map.mp hx
  have e := Finset.ne_of_mem_erase (ordered_factors_membership.mp h)
  omega

def derivativeMagnitudeRun (a : ℕ) (t : ℤ) : Meter (Word (derivativeWidth a+1)) :=
  magnitudeProduct (derivativeWidth a+1) ((orderedDerivative a t).map Int.natAbs)

theorem actual_grid_magnitude_receipt (a : ℕ) {t : ℤ} (mem : t∈grid a) :
    let w := derivativeWidth a+1
    let run := derivativeMagnitudeRun a t
    bitsValue run.result.val=((orderedDerivative a t).prod).natAbs ∧
      run.steps≤3*w+3+(2*2^a-1)*(wordOpCap w+6*w+8) ∧
      negativeParity (orderedDerivative a t)=decide ((orderedDerivative a t).prod<0) := by
  let l := (orderedDerivative a t).map Int.natAbs
  let w := derivativeWidth a+1
  have bound := every_native_derivative_prefix_fits a mem (orderedDerivative a t).length
  rw [List.take_length] at bound
  have C : (((orderedDerivative a t).prod).natAbs:ℤ)≤(2:ℤ)^derivativeWidth a := by
    rw [Int.natCast_natAbs]; exact bound
  have B : l.prod≤2^derivativeWidth a := by
    change ((orderedDerivative a t).map Int.natAbs).prod≤_
    rw [product_abs_is_magnitude]
    exact_mod_cast C
  have W : 0<w := Nat.succ_pos _
  have size : l.prod<2^w := by
    change l.prod<2^(derivativeWidth a+1)
    rw [pow_succ]
    have p : 0<(2:ℕ)^derivativeWidth a := by positivity
    omega
  have fee := (product_magnitude_modular w W l).2
  have len : l.length=2*2^a-1 := by
    simp only [l,List.length_map,ordered_derivative_len a mem]
  rw [len] at fee
  refine ⟨?_,fee,(product_sign_literal _ (nonzero_ordered_factors a t)).1⟩
  change bitsValue (magnitudeProduct w l).result.val=_
  rw [actual_magnitude_word_value W l size,product_abs_is_magnitude]

#print axioms product_magnitude_modular
#print axioms actual_magnitude_word_value
#print axioms product_abs_is_magnitude
#print axioms product_sign_literal
#print axioms actual_grid_magnitude_receipt
end
end J4R43LiteralOutside

