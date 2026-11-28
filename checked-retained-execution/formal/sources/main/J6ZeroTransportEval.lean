import J6ZeroTransport
import Mathlib.Algebra.Polynomial.Div

/-! Evaluating genuine finite native probes commutes with the precision
tower. A coefficient jet can be truncated at X^j precisely when the
weighted probe kills X^j in the receiving ring. -/
namespace J6ZeroTransport
open Polynomial
open scoped BigOperators Polynomial

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem transport_eval₂ (f : R→+*S) (g : S→+*T) (P : R[X]) (x : S) :
    g (P.eval₂ f x) = P.eval₂ (g.comp f) (g x) :=
  Polynomial.hom_eval₂ P f g x

theorem truncate_coefficients (f : R→+*S) (P : R[X]) (j : ℕ) :
    (P %ₘ (X^j)).map f = P.map f %ₘ (X^j) := by
  rw [Polynomial.map_modByMonic f ((monic_X (R:=R)).pow j),Polynomial.map_pow,map_X]

/-- Exact evaluation through a true nilpotent quotient, independent of
characteristic or a complete coefficient field. -/
theorem eval_truncated (f : R→+*S) (P : R[X]) (x : S) (j : ℕ) (h : x^j=0) :
    (P %ₘ X^j).eval₂ f x = P.eval₂ f x := by
  apply Polynomial.eval₂_modByMonic_eq_self_of_root ((monic_X (R:=R)).pow j)
  simp [Polynomial.eval₂_pow,h]

theorem pow_zero_above_precision (p j : ℕ) (h : (2:S)^p=0) (hle : p≤j) :
    (2:S)^j=0 := by
  obtain ⟨e,he⟩ := pow_dvd_pow (2:S) hle
  rw [he,h,zero_mul]

theorem weighted_probe_kills (p k j : ℕ) (h : (2:S)^p=0) (hle : p≤k*j) (z : S) :
    ((2:S)^k*z)^j=0 := by
  rw [mul_pow,← pow_mul,pow_zero_above_precision p _ h hle,zero_mul]

theorem eval_weighted_truncated (f : R→+*S) (P : R[X]) (z : S) (p k j : ℕ)
    (h : (2:S)^p=0) (hle : p≤k*j) :
    (P %ₘ X^j).eval₂ f ((2:S)^k*z) = P.eval₂ f ((2:S)^k*z) :=
  eval_truncated f P _ j (weighted_probe_kills p k j h hle z)

/-- Reducing a genuine native weighted probe from q to p before evaluating
and truncating gives exactly the same element. No low-to-high canonical
raising is assumed to preserve arithmetic. -/
theorem native_weighted_eval_precision (p q : ℕ) (hpq : p≤q) (poly : ℤ[X])
    (b : Fin poly.natDegree→Bool) (P : DenominatorBudget.TwoLocal[X])
    (k j : ℕ) (hle : p≤k*j) :
    NativeProbeRing.reduceScalar p q hpq poly
      (P.eval₂ (reduceNative q poly) ((2:NativeProbeRing.Scalar q poly)^k*
        NativeProbeRing.probe q poly b)) =
    (P %ₘ X^j).eval₂ (reduceNative p poly) ((2:NativeProbeRing.Scalar p poly)^k*
      NativeProbeRing.probe p poly b) := by
  rw [transport_eval₂,native_precision,map_mul,map_pow,map_ofNat,
    NativeProbeRing.same_probe_at_higher_precision]
  exact (eval_weighted_truncated _ _ _ p k j (NativeProbeRing.scalar_nilpotent p poly) hle).symm

/-- The literal ell=1 projection in the source identifies the class of a
polynomial with its evaluation at zero; reducing its coefficients and
taking its constant coordinate commute. -/
theorem ell_one_eval (f : R→+*S) (P : R[X]) :
    NativeProbeRing.truncateOne S (AdjoinRoot.mk (X:S[X]) (P.map f)) =
      f (P.coeff 0) := by
  change AdjoinRoot.lift (RingHom.id S) (0:S) (by simp) (AdjoinRoot.mk (X:S[X]) (P.map f)) = _
  rw [AdjoinRoot.lift_mk,Polynomial.eval₂_at_zero,Polynomial.coeff_map]
  rfl

/-- The finite reciprocal is coherent across arbitrary receiving homs when
the integer being inverted is actually odd. No compatibility is claimed
for trying to invert a raw denominator divisible by two. -/
theorem oddReciprocal_precision (f : S→+*T) (p q : ℕ)
    (hp : (2:S)^p=0) (hq : (2:T)^q=0) (d : ℤ) (odd : ¬(2:ℤ)∣d) :
    f (oddReciprocal S p d) = oddReciprocal T q d := by
  have ha := congrArg f (oddReciprocal_valid p hp d odd)
  rw [map_mul,map_intCast,map_one] at ha
  calc
    _ = f (oddReciprocal S p d) * ((d:T)*oddReciprocal T q d) := by
       rw [oddReciprocal_valid q hq d odd,mul_one]
    _ = ((d:T)*f (oddReciprocal S p d))*oddReciprocal T q d := by ac_rfl
    _ = _ := by rw [ha,one_mul]

#print axioms transport_eval₂
#print axioms truncate_coefficients
#print axioms eval_truncated
#print axioms pow_zero_above_precision
#print axioms weighted_probe_kills
#print axioms eval_weighted_truncated
#print axioms native_weighted_eval_precision
#print axioms ell_one_eval
#print axioms oddReciprocal_precision

end J6ZeroTransport