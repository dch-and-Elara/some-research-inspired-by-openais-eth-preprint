import V8NativeMessageN7LiteralSupportResidue
import V8NativeMessageN7LiteralSupportHeight
import V8NativeMessageN7LiteralSupportZero

/-! Exact denominator clearing in the old slot's actual receiving
ring, with the true root flags, signed mesh and read function. A small
shift window will use this finite bound; no centered or arbitrary
numeric input is assumed. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking P1DyadicGrid P1DyadicGridBridge DenominatorBudget
open J6R10Repack J6R9Recursive J6R9PacketCoeff J6R9PacketScopes
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option maxRecDepth 2200
noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]}
variable (P : PhysicalPacking N a G)
variable (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)

def rationalGrid (a : ℕ) (t : ℤ) : ℚ := derivRatio a t

def clearedActual (t : ℤ) : ℤ :=
  let q := rationalGrid a t
  J6NativeHeight.numerator (rowKeep N flags) (colKeep N flags) (readTrueShift P t)
    q.num q.den

theorem exact_cleared_of_zero_slot (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (mem : t∈grid a)
    (p₀ p : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree) :
    (clearedActual P flags t:Residue f 1 p)=
      ((rationalGrid a t).den:Residue f 1 p)^Fintype.card E *
        V8PooledMenu.slot P i ht hv p (J6R10Integral.box_two_nil p f 1) 0
          (V8PooledMenu.binaryFile f p₀ flags) hf 0 := by
  let q := rationalGrid a t
  let φ : TwoLocal→+*Residue f 1 p := J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f 1)
  have frac : twoLocalRat (J6R9PacketCoeff.rho a t)=(q.num:ℚ)/(q.den:ℚ) := by
    rw [J6R9PacketCoeff.rho_rat mem]
    exact q.num_div_den.symm
  have times : (q.den:Residue f 1 p)*φ (J6R9PacketCoeff.rho a t)=(q.num:Residue f 1 p) := by
    have h := J6NativeHeightResidue.scalarClearing φ (J6R9PacketCoeff.rho a t) q.num (q.den:ℤ)
      (by exact_mod_cast q.den_ne_zero) frac
    simpa using h
  rw [actual_zero_slot_is_reduction P i ht hv flags p₀ p hp₀ hf hd,exactZero,
    full_signed_root_is_zero_polynomial]
  change (clearedActual P flags t:Residue f 1 p)=_ * φ (signedRoot P i t (J6R9PacketCoeff.rho a t) flags)
  rw [map_signed_root,literal_signed_cube_is_residue_slot P i ht hv]
  have h := J6NativeHeightResidue.residueClearing (rowKeep N flags) (colKeep N flags) (readTrueShift P t)
    q.num (q.den:ℤ) (φ (J6R9PacketCoeff.rho a t)) (by simpa using times)
  simpa [clearedActual,q] using h


theorem exact_cleared_of_rational_root (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (mem : t∈grid a) :
    (clearedActual P flags t:ℚ)=
      ((rationalGrid a t).den:ℚ)^Fintype.card E * twoLocalRat (exactZero P i t flags) := by
  let q := rationalGrid a t
  have frac : twoLocalRat (J6R9PacketCoeff.rho a t)=(q.num:ℚ)/(q.den:ℚ) := by
    rw [J6R9PacketCoeff.rho_rat mem]
    exact q.num_div_den.symm
  have times := J6NativeHeightResidue.scalarClearing twoLocalRat (J6R9PacketCoeff.rho a t) q.num (q.den:ℤ)
    (by exact_mod_cast q.den_ne_zero) frac
  rw [exactZero,full_signed_root_is_zero_polynomial,map_signed_root,
    literal_signed_cube_is_residue_slot P i ht hv]
  have h := J6NativeHeightResidue.residueClearing (rowKeep N flags) (colKeep N flags) (readTrueShift P t)
    q.num (q.den:ℤ) (twoLocalRat (J6R9PacketCoeff.rho a t)) times
  simpa [clearedActual,q] using h

theorem actual_cleared_has_finite_height {t : ℤ} (mem : t∈grid a) :
    |clearedActual P flags t|≤(2:ℤ)^(Fintype.card E*(3+(a+1)*(t.natAbs+1))) := by
  let q := rationalGrid a t
  let s := (a+1)*(t.natAbs+1)
  let C : ℤ := 2^s
  let Cn : ℕ := 2^s
  have cc : (Cn:ℤ)=C := by simp [Cn,C]
  have B := (real_grid_reduced_height mem).2
  have L : (2*(2:ℕ)^a)^(t.natAbs+1)=2^s := by
    rw [←pow_succ',←pow_mul]
  rw [L] at B
  have nq : q.num.natAbs≤2^s := (le_max_left _ _).trans B
  have dq : q.den≤2^s := (le_max_right _ _).trans B
  have hn : |q.num|≤C := by
    rw [←Int.natCast_natAbs]
    have hcast : (q.num.natAbs:ℤ)≤(Cn:ℤ) := Int.ofNat_le.mpr nq
    simpa only [cc] using hcast
  have hd : |(q.den:ℤ)|≤C := by
    rw [abs_of_nonneg (by positivity)]
    have hcast : (q.den:ℤ)≤(Cn:ℤ) := Int.ofNat_le.mpr dq
    simpa only [cc] using hcast
  have b := J6NativeHeight.numerator_abs (rowKeep N flags) (colKeep N flags) (readTrueShift P t)
    q.num q.den C hn hd
  change |clearedActual P flags t|≤_
  refine b.trans_eq ?_
  dsimp only [C]
  rw [←pow_succ',←pow_mul,←pow_add]
  congr 1
  unfold s
  ring

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.exact_cleared_of_zero_slot
#print axioms V8NativeMessage.N7LiteralSupport.actual_cleared_has_finite_height

#print axioms V8NativeMessage.N7LiteralSupport.exact_cleared_of_rational_root
