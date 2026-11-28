import J6ZeroTransportSource
import J6ZeroTransportQuotient
import J6ZeroTransportEval

/-! The same high-precision literal slot can be used by a lower-precision
receiver. This closes the zero-mode route through the genuine lifted
extension and the ell=1 quotient, before the exact centered integer read. -/
namespace J6ZeroTransport

open scoped Classical
open DenominatorBudget J6Mesh J6PhysicalPacking J6NativeHeightMesh

/-- Binary source with the additional V-jet quotient at ell=1. The lifted
zero-probe zero-mode coefficient is constant in that quotient. -/
noncomputable def extensionZeroSlot {C : Type*} [Fintype C] [DecidableEq C]
    (q : ℕ) (poly : Polynomial ℤ) (rho : C) (m l : ℕ) (h : m≤K m)
    (i : Fin (m+1)) (A B : (Wire rho m (K m) l→Bool)→Bool) :
    AdjoinRoot (Polynomial.X : Polynomial (NativeProbeRing.Scalar q poly)) :=
  AdjoinRoot.of _ (reduceNative q poly (localContraction rho m l h i A B))

theorem extensionZero_receives_at {C : Type*} [Fintype C] [DecidableEq C]
    (p q : ℕ) (hpq : p≤q) (poly : Polynomial ℤ) (rho : C)
    (m l : ℕ) (h : m≤K m) (i : Fin (m+1))
    (A B : (Wire rho m (K m) l→Bool)→Bool) :
    NativeProbeRing.reduceScalar p q hpq poly
      (NativeProbeRing.truncateOne (NativeProbeRing.Scalar q poly)
        (extensionZeroSlot q poly rho m l h i A B)) =
      reduceNative p poly (localContraction rho m l h i A B) := by
  unfold extensionZeroSlot
  rw [truncate_one_base]
  change ((NativeProbeRing.reduceScalar p q hpq poly).comp (reduceNative q poly))
      (localContraction rho m l h i A B) = _
  rw [native_precision]

/-- For the actual source lift, lowering its immutable extension slot and
extracting the constant coordinate gives the exact printed base residue. -/
theorem extensionZero_base_at {C : Type*} [Fintype C] [DecidableEq C]
    (p q : ℕ) (hpq : p≤q) (hp : 0<p) (poly : Polynomial ℤ)
    (hmon : poly.Monic) (hdegree : 0<poly.natDegree)
    (rho : C) (m l : ℕ) (h : m≤K m) (i : Fin (m+1))
    (A B : (Wire rho m (K m) l→Bool)→Bool) :
    NativeProbeRing.projectBase p poly hmon
      (NativeProbeRing.reduceScalar p q hpq poly
        (NativeProbeRing.truncateOne (NativeProbeRing.Scalar q poly)
          (extensionZeroSlot q poly rho m l h i A B))) =
      reduceBase p (localContraction rho m l h i A B) := by
  rw [extensionZero_receives_at,native_constant_projection _ hp _ _ hdegree]

/-- Direct exact read of the literal high native zero-mode at the printed
receiving precision; the result equals the original rational source sum. -/
theorem exact_from_extension {C : Type*} [Fintype C] [DecidableEq C]
    (m base q : ℕ) (hpq : J6SourcePrecision.printed m base ≤ q)
    (hp : 0<J6SourcePrecision.printed m base) (poly : Polynomial ℤ)
    (hmon : poly.Monic) (hdegree : 0<poly.natDegree)
    (rho : C) (l : ℕ) (h : m≤K m) (hW : Fintype.card (Wire rho m (K m) l)=M m)
    (i : Fin (m+1)) (A B : (Wire rho m (K m) l→Bool)→Bool) :
    let p := J6SourcePrecision.printed m base
    let native := NativeProbeRing.projectBase p poly hmon
      (NativeProbeRing.reduceScalar p q hpq poly
        (NativeProbeRing.truncateOne (NativeProbeRing.Scalar q poly)
          (extensionZeroSlot q poly rho m l h i A B)))
    ((((sampleDen m i : ZMod (2^p))^M m*native).valMinAbs:ℚ) /
      (sampleDen m i:ℚ)^M m) = J6NativeHeightKernel.sourceContraction rho m l h i A B := by
  dsimp only
  rw [extensionZero_base_at _ _ hpq hp _ _ hdegree]
  exact centered_literal m base rho l h hW i A B

#print axioms extensionZero_receives_at
#print axioms extensionZero_base_at
#print axioms exact_from_extension

end J6ZeroTransport