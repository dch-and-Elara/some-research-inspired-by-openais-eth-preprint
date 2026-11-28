import J4R43LiteralOutsideGeometry
import J8EndToEndAmplitude
import V8NativeMessageN7LiteralSupportOrientation
import V8NativeMessageN7HighBoundReceipt

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7200000

/-! The actual signed scalar at the positive exterior node, and the
native printed p_t. Neither a supplied kernel nor a width condition on
the positive integer is allowed to change the physical source center. -/
namespace J4R43LiteralOutside
open P1DyadicGrid P1DyadicGridBridge DenominatorBudget J6R9PacketCoeff
open Polynomial J6DeformationPoly J8Physical J8EndToEnd
open P11FullPacking J6R10Repack V8NativeMessage.N7LiteralSupport Paper5.HybridClosure
open V8NativeMessage.N7HighBound J6R9Recursive Paper5.D1Literal
open J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted
open scoped Polynomial Classical BigOperators

noncomputable section

theorem actual_grid_as_printed (a : ℕ) :
    grid a = printedGrid (2^a) := by
  ext t
  rw [mem_grid,printedGrid,Finset.mem_Ico]
  simp only [pow₂,Nat.cast_pow,Nat.cast_ofNat]

theorem printed_derivative_product (a : ℕ) {t : ℤ} (h : t∈grid a) :
    (((cauchyPolynomial a).derivative.eval t:ℤ):ℚ) = derivativeProduct (2^a) t := by
  rw [cauchy_derivative_eval h,Int.cast_prod,derivativeProduct,←actual_grid_as_printed]

theorem genuine_extreme_mem (a : ℕ) : (((2^a:ℕ):ℤ)-1)∈grid a := by
  rw [mem_grid]
  simp only [pow₂,Nat.cast_pow,Nat.cast_ofNat]
  have h : 0<(2:ℤ)^a := by positivity
  omega

theorem actual_kernel_at_extreme (a : ℕ) (ha : 0<a) :
    rho a (((2^a:ℕ):ℤ)-1) = (J9FactorBounds.kernel (2^a):TwoLocal) := by
  have even : Even ((2:ℕ)^a) := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    rw [hd,pow_succ]
    exact ⟨2^d,by omega⟩
  have hL : 1≤(2:ℕ)^a := Nat.succ_le_of_lt (pow_pos (by decide) _)
  apply twoLocalRat_injective
  rw [rho_rat (genuine_extreme_mem a),map_intCast,printed_amplitude_integral _ hL even,
    derivRatio,outerAmplitude,printed_derivative_product a (genuine_extreme_mem a),
    printed_derivative_product a (zero_mem_grid a)]

theorem genuine_extreme_negative (a : ℕ) :
    J9FactorBounds.kernel (2^a)<0 := by
  have hL : 1≤(2:ℕ)^a := Nat.succ_le_of_lt (pow_pos (by decide) _)
  unfold J9FactorBounds.kernel
  have hb : 0 < (2*2^a-1).choose (2^a) := Nat.choose_pos (by omega)
  exact neg_neg_of_pos (by exact_mod_cast hb)

variable {E A B G : Type} [LinearOrder G] [Fintype G] [Fintype E]
variable {a : ℕ} {N : Network E A B}

theorem genuine_extreme_matches_budget (P : PhysicalPacking N a G) :
    Nat.card (Matching P (((2^a:ℕ):ℤ)-1))*(2*2^a) ≤ 6*Fintype.card E := by
  let L := (2:ℕ)^a
  let M := Fintype.card E
  have hL : 1≤L := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have ha : ((L:ℤ)-1).natAbs=L-1 := by
    change ((L:ℤ)-((1:ℕ):ℤ)).natAbs=L-1
    rw [←Nat.cast_sub hL,Int.natAbs_natCast]
  have hk := actual_matches_at_most_padded_range P (((L:ℕ):ℤ)-1)
  change Nat.card (Matching P ((L:ℤ)-1))≤(3*M/L)*(L-((L:ℤ)-1).natAbs) at hk
  rw [ha,show L-(L-1)=1 by omega,mul_one] at hk
  change Nat.card (Matching P ((L:ℤ)-1))*(2*L)≤6*M
  calc
    _ ≤ (3*M/L)*(2*L) := Nat.mul_le_mul_right _ hk
    _ = 2*((3*M/L)*L) := by ac_rfl
    _ ≤ 2*(3*M) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = _ := by ring

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "s" => (oldRowSize F)
local notation "S" => (printedParams (f:=f) (ell:=1) s)
local notation "root" => (oldColumnRoot F reg f (fun _=>false))
local notation "M" => (Fintype.card (DWire F))

theorem opposite_printed_precision (t : ColumnCenter F reg (f:=f)) :
    8*M*((S).levelBits 0+1)+1 ≤ registerPrecision S root t := by
  change 8*M*((S).levelBits 0+1)+1 ≤
    J9PrintedSchedule.precision (4*Fintype.card W+1)
      (J6ActiveSchedule.height M ((S).levelWidth 0))
      (2^(S).levelBits 0/2^padicValInt 2 t.val) M ((S).levelBits 0)
  unfold J9PrintedSchedule.precision
  omega

theorem actual_extreme_integer_lift (t : ColumnCenter F reg (f:=f))
    (positive : 0<M) (hf : f.Monic) (hd : 0<f.natDegree)
    (z : ℤ) (hz : |z|≤(2:ℤ)^(7*M)) :
    let p := registerPrecision S root t
    centeredBox p f hf (z:Residue f 1 p)=z := by
  let p := registerPrecision S root t
  have hlow := opposite_printed_precision F reg t
  have hb : 8*M≤8*M*((S).levelBits 0+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have shift : 7*M+1<p := by omega
  apply centered_box_recovers p (by omega) f hf hd z
  calc
    2*|z| ≤ 2*(2:ℤ)^(7*M) := Int.mul_le_mul_of_nonneg_left hz (by decide)
    _ = (2:ℤ)^(7*M+1) := by rw [pow_succ',mul_comm]
    _ < (2:ℤ)^p := pow_lt_pow_right₀ (by decide) shift

#print axioms actual_grid_as_printed
#print axioms printed_derivative_product
#print axioms actual_kernel_at_extreme
#print axioms genuine_extreme_negative
#print axioms genuine_extreme_matches_budget
#print axioms opposite_printed_precision
#print axioms actual_extreme_integer_lift

end
end J4R43LiteralOutside



