import J6NativeHeightDyadic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

/-! Integer lifting of the J6 completed zero mode. The sole native
premise is equality of the delivered value to the displayed same-packet
residue contraction with the two-local mesh scalar. -/
namespace J6NativeHeightLift
open scoped BigOperators
open J6Mesh J6NativeHeight J6NativeHeightClearing J6NativeHeightMesh
open J6NativeHeightResidue J6NativeHeightDyadic
variable {P : Type*} [Fintype P] [DecidableEq P]

theorem exact_centered_readout (m base : ℕ) (i : Fin (m+1))
    (hP : Fintype.card P = M m)
    (A B : (P → Bool) → Bool) (read : P → (P → Bool) → Bool)
    (f : DenominatorBudget.TwoLocal →+* ZMod (2^J6SourcePrecision.printed m base))
    (native : ZMod (2^J6SourcePrecision.printed m base))
    (realizes : native = residueSlot A B read (f (scalar m i))) :
    ((((sampleDen m i : ZMod (2^J6SourcePrecision.printed m base))^M m*native).valMinAbs : ℚ) /
      (sampleDen m i : ℚ)^M m) = rationalSlot A B read (point m i) := by
  let p := J6SourcePrecision.printed m base
  let d := sampleDen m i
  let n := sampleNum m i
  let num := numerator A B read n d
  have ⟨hd,hn,hdB⟩ := mesh_bounds m i
  letI : NeZero ((2:ℕ)^p) := ⟨pow_ne_zero _ (by decide)⟩
  have hB : 2*|num| < (↑((2:ℕ)^p):ℤ) :=
    J6SourcePrecision.centered_fit_printed m base i num
      (physical_height m (index m i) hP A B read n d hn hdB)
  have hq : (num : ℚ) = (d:ℚ)^M m * rationalSlot A B read (point m i) := by
    have h := explicit_cleared_numerator A B read n d hd.ne'
    rwa [hP,← mesh_fraction] at h
  have hnR := residueClearing A B read n d (f (scalar m i)) (actual_scalar_clearing f m i)
  have hs : ((d:ZMod (2^p))^M m*native).valMinAbs = num := by
    apply (ZMod.valMinAbs_spec _ _).mpr
    constructor
    · rw [← realizes,hP] at hnR
      exact hnR.symm
    · change -(↑((2:ℕ)^p):ℤ) < num*2 ∧ num*2 ≤ ↑((2:ℕ)^p)
      constructor <;> linarith [le_abs_self num,neg_le_abs num]
  change (((((d : ZMod (2^p))^M m*native).valMinAbs : ℚ)) /
    (d : ℚ)^M m) = _
  rw [hs,hq,mul_div_cancel_left₀]
  exact pow_ne_zero _ (by exact_mod_cast hd.ne')

#print axioms exact_centered_readout
end J6NativeHeightLift
