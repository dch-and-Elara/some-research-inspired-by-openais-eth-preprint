import V8NativeMessageN7LiteralSupportFactor
import V8NativeMessageN7LiteralSupportSigned
import V8NativeMessageN7LiteralSupportZero

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14500000
set_option maxRecDepth 2100

/-! The exact original normalized unit shift is an integer. The
integer is formed by the same source contraction; this file neither
chooses a chart nor replaces a host. -/
namespace V8NativeMessage.N7HighBound
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
  V8NativeMessage.N7LiteralSupport

noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a)
variable (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)

def unitInteger : ℤ := signedRoot P i (-1) (-1:ℤ) flags

theorem exact_unit_integer :
    exactZero P i (-1) flags=(unitInteger P i flags:TwoLocal) := by
  unfold exactZero
  rw [full_signed_root_is_zero_polynomial,rho_at_actual_unit_shift]
  have h := map_signed_root P i (Int.castRingHom TwoLocal) (-1:ℤ) (-1) flags
  simpa only [Int.coe_castRingHom,map_neg,map_one,unitInteger] using h.symm

theorem exact_unit_zero_iff :
    exactZero P i (-1) flags=0 ↔ unitInteger P i flags=0 := by
  rw [exact_unit_integer]
  constructor
  · intro h
    have H := congrArg twoLocalRat h
    rw [map_intCast,map_zero] at H
    exact_mod_cast H
  · intro h
    rw [h,Int.cast_zero]

variable {f : ℤ[X]}

def nativeUnitZeroSlot (hv : padicValInt 2 (-1)=i.val)
    (p₀ p : ℕ) (hf : f.Monic) : Box f 1 p :=
  V8PooledMenu.slot P i (by norm_num : (-1:ℤ)≠0) hv p (J6R10Integral.box_two_nil p f 1) 0
    (V8PooledMenu.binaryFile f p₀ flags) hf 0

theorem actual_unit_slot_is_integer (hv : padicValInt 2 (-1)=i.val)
    (p₀ p : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree) :
    nativeUnitZeroSlot P i flags hv p₀ p hf=(unitInteger P i flags:Box f 1 p) := by
  unfold nativeUnitZeroSlot
  rw [actual_zero_slot_is_reduction P i (by norm_num) hv flags p₀ p hp₀ hf hd,
    exact_unit_integer,J6ZeroTransport.reduceAt_int]

#print axioms exact_unit_integer
#print axioms exact_unit_zero_iff
#print axioms actual_unit_slot_is_integer
end
end V8NativeMessage.N7HighBound
