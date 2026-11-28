import J6R9RecursiveCanonical
import J6ActiveRun

/-! Genuine precision transport in both native quotient variables.
Lowering is a ring map; raising a stored coordinate word uses its
canonical integer representatives and is not asserted to be additive. -/
namespace J6R10Reachable
open scoped Polynomial
open Polynomial J6R9Recursive J6ActiveRun

noncomputable def lower (p q : ℕ) (hle : p ≤ q) (f : ℤ[X]) (ell : ℕ) :
    J6ActiveInterpolation.Ring q f ell →+* J6ActiveInterpolation.Ring p f ell :=
  adjoinMap (NativeProbeRing.reduceScalar p q hle f) _ _ (by simp)

theorem lower_integral_scalar (p q : ℕ) (hle : p ≤ q) (f : ℤ[X]) :
    (NativeProbeRing.reduceScalar p q hle f).comp (J6R9Recursive.reduceScalar q f) =
      J6R9Recursive.reduceScalar p f := by
  apply RingHom.ext
  intro x
  obtain ⟨x,rfl⟩ := AdjoinRoot.mk_surjective x
  unfold J6R9Recursive.reduceScalar
  simp only [RingHom.comp_apply,adjoinMap_mk,NativeProbeRing.reduceScalar_mk,
    Polynomial.map_map,J6ZeroTransport.base_precision p q hle]

theorem lower_integral (p q : ℕ) (hle : p ≤ q) (f : ℤ[X]) (ell : ℕ) :
    (lower p q hle f ell).comp (reduce q f ell) = reduce p f ell := by
  apply RingHom.ext
  intro x
  obtain ⟨x,rfl⟩ := AdjoinRoot.mk_surjective x
  unfold lower reduce
  simp only [RingHom.comp_apply,adjoinMap_mk,Polynomial.map_map,lower_integral_scalar p q hle f]

noncomputable def raise (p q : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (x : J6ActiveInterpolation.Ring p f ell) : J6ActiveInterpolation.Ring q f ell :=
  reduce q f ell (canonicalLift p f hf ell x)

theorem lower_raise (p q : ℕ) (hle : p ≤ q) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (x : J6ActiveInterpolation.Ring p f ell) :
    lower p q hle f ell (raise p q f hf ell x) = x := by
  unfold raise
  change ((lower p q hle f ell).comp (reduce q f ell)) (canonicalLift p f hf ell x) = x
  rw [lower_integral p q hle f ell,canonicalLift_spec]

theorem lower_probes (p q : ℕ) (hle : p ≤ q) (f : ℤ[X]) (ell d : ℕ)
    (fit : d ≤ 2^f.natDegree) (i : Fin d) :
    lower p q hle f ell (J6ActiveInterpolation.node q f ell d fit i) =
      J6ActiveInterpolation.node p f ell d fit i := by
  unfold lower J6ActiveInterpolation.node J6ActiveInterpolation.scalarIn
  rw [adjoinMap_of,NativeProbeRing.same_probe_at_higher_precision]

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {S : Shape Host Mode}

theorem active_child_precision_transport (f : ℤ[X]) (ell : ℕ)
    (P : Program S (fun p => J6ActiveInterpolation.Ring p f ell))
    (c : Call Host) (hc : S.cutoff < c.edges) (w : Address S c) (x : IntRing f ell) :
    lower c.prec (P.child c w).prec (P.child_higher_precision c hc w).le f ell
        (reduce (P.child c w).prec f ell x) = reduce c.prec f ell x :=
  DFunLike.congr_fun (lower_integral _ _ (P.child_higher_precision c hc w).le f ell) x

#print axioms lower_integral_scalar
#print axioms lower_integral
#print axioms lower_raise
#print axioms lower_probes
#print axioms active_child_precision_transport
end J6R10Reachable