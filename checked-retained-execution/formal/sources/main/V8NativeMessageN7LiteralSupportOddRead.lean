import V8NativeMessageN7LiteralSupportCleared
import V8NativeMessageN7LiteralSupportOddWindow
import V8NativeMessageN7HighBoundReceipt

/-! At a small signed odd displacement, zero versus nonzero of the
original rational zero-mode value survives its actual finite receiver.
The rational and native expressions refer to the same physical input. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial
open Polynomial DenominatorBudget P1DyadicGrid P11FullPacking
open J6R10Repack J6R9Recursive J6R9PacketScopes J6R12Blueprint J6ActiveRun
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7 V8NativeMessage.N7HighBound
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14000000
set_option maxRecDepth 2600
noncomputable section

section General
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]}
variable (P : PhysicalPacking N a G)
variable (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)

theorem finite_zero_iff_exact_same_rational
    (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (mem : t∈grid a)
    (p₀ p : ℕ) (hp₀ : 0<p₀) (hp : 0<p) (hf : f.Monic) (hd : 0<f.natDegree)
    (room : Fintype.card E*clearedExponent a t<p) :
    V8PooledMenu.slot P i ht hv p (J6R10Integral.box_two_nil p f 1) 0
      (V8PooledMenu.binaryFile f p₀ flags) hf 0 = 0 ↔
        exactZero P i t flags=0 := by
  let q := rationalGrid a t
  let W := V8PooledMenu.slot P i ht hv p (J6R10Integral.box_two_nil p f 1) 0
    (V8PooledMenu.binaryFile f p₀ flags) hf 0
  let Z := clearedActual P flags t
  let M := Fintype.card E
  have odd : Odd (q.den:ℤ) := (real_grid_reduced_height mem).1
  have atom := J6ZeroTransport.oddCast_unit (S:=Residue f 1 p) p
    (J6R10Integral.box_two_nil p f 1) (q.den:ℤ)
    (fun even => (Int.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr even))
  have factor : IsUnit ((q.den:Residue f 1 p)^M) := by
    simpa only [Int.cast_natCast] using atom.pow M
  have nativeEq : (Z:Residue f 1 p)=(q.den:Residue f 1 p)^M*W :=
    exact_cleared_of_zero_slot P flags i ht hv mem p₀ p hp₀ hf hd
  have B : |Z|<(2:ℤ)^p := by
    refine (actual_cleared_has_finite_height P flags mem).trans_lt ?_
    exact pow_lt_pow_right₀ (by decide : (1:ℤ)<2) room
  have nv : W=0 ↔ Z=0 := by
    rw [←integer_box_zero_iff_of_height p hp f hf hd Z B,nativeEq]
    constructor
    · intro z
      rw [z,mul_zero]
    · intro h
      apply factor.mul_left_cancel
      rw [h,mul_zero]
  have rationalEq : (Z:ℚ)=(q.den:ℚ)^M*twoLocalRat (exactZero P i t flags) :=
    exact_cleared_of_rational_root P flags i ht hv mem
  have denNZ : (q.den:ℚ)^M≠0 := pow_ne_zero _ (by exact_mod_cast q.den_ne_zero)
  have rv : Z=0 ↔ exactZero P i t flags=0 := by
    constructor
    · intro r
      apply twoLocalRat_injective
      have y : (q.den:ℚ)^M*twoLocalRat (exactZero P i t flags)=0 := by
        rw [←rationalEq,r,Int.cast_zero]
      rw [map_zero]
      exact (mul_eq_zero.mp y).resolve_left denNZ
    · intro r
      have y : (Z:ℚ)=0 := by rw [rationalEq,r,map_zero,mul_zero]
      exact_mod_cast y
  exact nv.trans rv

end General

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "a" => (J6ActiveRun.Shape.levelBits (S) 0)
local notation "u" => (J6ActiveRun.Shape.levelWidth (S) 0)
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

theorem original_small_odd_zero_mode_preserves_exact_support
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (odd : Odd x.1.val) (zeroProbe : siteProbe F reg d x.1 x.2.1=0) (zeroMode : x.2.2.val=0)
    (small : clearedExponent a x.1.val*u<24*2^a) :
    wholePublic F reg P d hf σ x=0 ↔
      exactZero P (PublicIndex F reg f d x.1) x.1.val (oldRowTruth F reg σ)=0 := by
  rw [publicSlot_is_literal,zeroProbe,zeroMode]
  exact finite_zero_iff_exact_same_rational P (oldRowTruth F reg σ)
    (PublicIndex F reg f d x.1) (centerNonzero x.1) rfl (public_center_in_grid F reg x.1)
    (4*Fintype.card W+1) (sitePrecision F reg x.1) (by omega) ((Nat.zero_le _).trans_lt (original_high_precision_exceeds_four_edges F reg x.1)) hf hd
    (actual_small_odd_bit_window F reg d x.1 odd small)

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.finite_zero_iff_exact_same_rational
#print axioms V8NativeMessage.N7LiteralSupport.original_small_odd_zero_mode_preserves_exact_support
