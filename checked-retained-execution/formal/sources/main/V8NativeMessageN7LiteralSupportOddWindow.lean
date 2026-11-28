import V8NativeMessageN7LiteralSupportZero

/-! Quantitative receiving precision for the actual odd centres of the
old-row four-clone public menu. A finite small-shift guard suffices;
no asymptotic sequence or arbitrary root schedule is substituted. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial
open Polynomial J6R10Repack P1DyadicGrid J6ActiveRun J6R12Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000
set_option maxRecDepth 2200

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "u" => (J6ActiveRun.Shape.levelWidth (S) 0)
local notation "a" => (J6ActiveRun.Shape.levelBits (S) 0)
local notation "M" => (Fintype.card (DWire F))

def clearedExponent (a₀ : ℕ) (t : ℤ) := 3+(a₀+1)*(t.natAbs+1)

theorem actual_odd_site_has_precision_budget (t : PublicCenter F reg f) (odd : Odd t.val) :
    0<u ∧ 24*M*2^a ≤ sitePrecision F reg t*u := by
  have heard := t.property
  change t.val∈J6ActiveSchedule.active a M u at heard
  have q := (Finset.mem_filter.mp heard).2
  have hu : 0<u := by
    by_contra! nq
    have eq : u=0 := by omega
    simp [J6ActiveSchedule.order,eq] at q
  have hceil : 3*M≤J6ActiveSchedule.height M u*u :=
    J9PrintedSchedule.le_roundup_mul (3*M) u hu
  have valuation := odd_valuation_zero odd
  have pos : 8*J6ActiveSchedule.height M u*2^a≤sitePrecision F reg t := by
    change _≤J9PrintedSchedule.precision (4*Fintype.card W+1)
      (J6ActiveSchedule.height M u) (2^a/2^padicValInt 2 t.val) M a
    rw [valuation,pow_zero,Nat.div_one]
    unfold J9PrintedSchedule.precision
    omega
  refine ⟨hu,?_⟩
  calc
    24*M*2^a = (3*M)*(8*2^a) := by ring
    _ ≤ (J6ActiveSchedule.height M u*u)*(8*2^a) := Nat.mul_le_mul_right _ hceil
    _ = (8*J6ActiveSchedule.height M u*2^a)*u := by ring
    _ ≤ sitePrecision F reg t*u := Nat.mul_le_mul_right _ pos

theorem actual_small_odd_bit_window
    (d : N6PublicReady F reg (f:=f)) (t : PublicCenter F reg f) (odd : Odd t.val)
    (small : clearedExponent a t.val*u<24*2^a) :
    M*clearedExponent a t.val < sitePrecision F reg t := by
  have hm : 0<M := Nat.zero_lt_of_lt d.active
  obtain ⟨hu,budget⟩ := actual_odd_site_has_precision_budget F reg t odd
  have left : (M*clearedExponent a t.val)*u<sitePrecision F reg t*u := by
    calc
      _ = M*(clearedExponent a t.val*u) := by ring
      _ < M*(24*2^a) := Nat.mul_lt_mul_of_pos_left small hm
      _ = 24*M*2^a := by ring
      _ ≤ _ := budget
  exact Nat.lt_of_mul_lt_mul_right left

end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_odd_site_has_precision_budget
#print axioms V8NativeMessage.N7LiteralSupport.actual_small_odd_bit_window
