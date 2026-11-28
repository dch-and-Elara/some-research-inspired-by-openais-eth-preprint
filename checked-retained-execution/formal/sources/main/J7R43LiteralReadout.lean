import J7R43LiteralProbe

/-! Finite receiving-ring values are interpreted as literal nonnegative
integers only after a magnitude proof. No equality of the canonical
creation-time coefficient lifts with signed original coefficients is used. -/
namespace J7R43Literal
open scoped Polynomial Classical
open Polynomial NativeProbeRing J6ActiveInterpolation J6R14SpecializedBox J6R9Recursive
noncomputable section
set_option autoImplicit false

variable {f : ℤ[X]} {ell : ℕ}
def readUnsigned (p : ℕ) (hf : f.Monic) (hℓ : 0<ell) (R : Box f ell p) : ℕ :=
  (projectBase p f hf (atZero p f ell hℓ R)).val

theorem readUnsigned_exact (p : ℕ) (hp : 0<p) (hf : f.Monic) (hF : 0<f.natDegree)
    (hℓ : 0<ell) (n : ℕ) (hn : n<2^p) :
    readUnsigned p hf hℓ (n : Box f ell p) = n := by
  unfold readUnsigned
  rw [← map_natCast (scalarIn p f ell), atZero_scalarIn]
  rw [← map_natCast (AdjoinRoot.of (liftPoly p f)), projectBase_left p hp f hf hF]
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hn

theorem readUnsigned_exact_int (p : ℕ) (hp : 0<p) (hf : f.Monic) (hF : 0<f.natDegree)
    (hℓ : 0<ell) (n : ℤ) (nonneg : 0≤n) (fits : n.toNat<2^p) :
    (readUnsigned p hf hℓ (n : Box f ell p) : ℤ) = n := by
  have hn : (n.toNat : ℤ) = n := Int.toNat_of_nonneg nonneg
  rw [← hn,Int.cast_natCast,readUnsigned_exact p hp hf hF hℓ n.toNat fits]
#print axioms readUnsigned_exact
#print axioms readUnsigned_exact_int
end
end J7R43Literal