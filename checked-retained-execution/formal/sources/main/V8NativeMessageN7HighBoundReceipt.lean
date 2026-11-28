import J6R15SignedReadBase
import Mathlib.Data.ZMod.ValMinAbs

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

/-! Integer constants in the actual finite receiving ring. The positive
degree monic source modulus permits a faithful base-residue readout. -/
namespace V8NativeMessage.N7HighBound
open scoped Classical Polynomial
open Polynomial DenominatorBudget J6R9Recursive

noncomputable section

def centeredBox (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (u : Box f 1 p) : ℤ :=
  (J6R15SignedRead.boxProject p f 1 hf (by decide) u).valMinAbs

theorem project_integer (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0<f.natDegree) (z : ℤ) :
    J6R15SignedRead.boxProject p f 1 hf (by decide) (z:Box f 1 p)=(z:NativeProbeRing.Base p) := by
  simpa only [map_intCast] using
    J6R15SignedRead.boxProject_base p f 1 hf hp hd (by decide) (z:NativeProbeRing.Base p)

theorem integer_box_zero_iff_dvd (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0<f.natDegree) (z : ℤ) :
    (z:Box f 1 p)=0 ↔ (2:ℤ)^p∣z := by
  have hChar : (z:NativeProbeRing.Base p)=0 ↔ (2:ℤ)^p∣z := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      (CharP.intCast_eq_zero_iff (NativeProbeRing.Base p) (2^p) z)
  constructor
  · intro hz
    have h := congrArg (J6R15SignedRead.boxProject p f 1 hf (by decide)) hz
    have z₀ : J6R15SignedRead.boxProject p f 1 hf (by decide) (0:Box f 1 p)=0 := by
      simpa only [Int.cast_zero] using project_integer p hp f hf hd 0
    rw [project_integer p hp f hf hd z,z₀] at h
    exact hChar.mp h
  · intro dz
    have h := congrArg (J6R15SignedRead.boxBase p f 1) (hChar.mpr dz)
    simpa only [map_zero,map_intCast] using h

theorem integer_box_zero_iff_of_height (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0<f.natDegree) (z : ℤ) (height : |z|<(2:ℤ)^p) :
    (z:Box f 1 p)=0 ↔ z=0 := by
  constructor
  · intro h
    apply @Int.eq_zero_of_abs_lt_dvd ((2:ℤ)^p)
    · exact (integer_box_zero_iff_dvd p hp f hf hd z).mp h
    · exact height
  · rintro rfl
    exact Int.cast_zero

theorem centered_box_recovers (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0<f.natDegree) (z : ℤ) (height : 2*|z|<(2:ℤ)^p) :
    centeredBox p f hf (z:Box f 1 p)=z := by
  letI : NeZero ((2:ℕ)^p) := ⟨pow_ne_zero _ (by decide)⟩
  rw [centeredBox,project_integer p hp f hf hd z]
  apply (ZMod.valMinAbs_spec _ _).2
  refine ⟨rfl,?_⟩
  change -(↑((2:ℕ)^p):ℤ)<z*2 ∧ z*2≤↑((2:ℕ)^p)
  push_cast
  constructor <;> linarith only [height,le_abs_self z,neg_le_abs z]

theorem reduce_integer_box_zero_iff (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0<f.natDegree) (x : TwoLocal) (z : ℤ) (real : x=(z:TwoLocal))
    (height : |z|<(2:ℤ)^p) :
    J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f 1) x=0 ↔ z=0 := by
  rw [real,J6ZeroTransport.reduceAt_int]
  exact integer_box_zero_iff_of_height p hp f hf hd z height

#print axioms project_integer
#print axioms integer_box_zero_iff_dvd
#print axioms integer_box_zero_iff_of_height
#print axioms centered_box_recovers
#print axioms reduce_integer_box_zero_iff
end
end V8NativeMessage.N7HighBound
