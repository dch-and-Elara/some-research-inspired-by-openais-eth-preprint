import J6ZeroTransport
import J6NativeHeightResidue
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Characterize the receiving base ring as the actual source quotient:
the kernel is exactly 2^p, not just a containment. -/
namespace J6ZeroTransport

open DenominatorBudget

local instance : IsLocalization atTwoPrime.primeCompl TwoLocal := by
  unfold TwoLocal twoLocalSubalgebra
  infer_instance

theorem source_odd_unit (d : ℤ) (h : ¬(2:ℤ)∣d) : IsUnit (d:TwoLocal) := by
  let u : atTwoPrime.primeCompl := ⟨d,by
    simpa only [atTwoPrime,Ideal.mem_primeCompl_iff,Ideal.mem_span_singleton] using h⟩
  exact IsLocalization.map_units TwoLocal u

theorem reduceBase_surjective (p : ℕ) : Function.Surjective (reduceBase p) := by
  letI : NeZero ((2:ℕ)^p) := ⟨pow_ne_zero _ (by decide)⟩
  intro x
  refine ⟨(x.val:TwoLocal),?_⟩
  rw [map_natCast,ZMod.natCast_zmod_val]

theorem reduceBase_zero_iff (p : ℕ) (x : TwoLocal) :
    reduceBase p x=0 ↔ (2:TwoLocal)^p ∣ x := by
  constructor
  · intro h
    obtain ⟨n,d,odd,hx⟩ := (mem_twoLocal_iff (x:ℚ)).mp x.prop
    have hd : d≠0 := fun hz => odd (hz ▸ dvd_zero (2:ℤ))
    have hEq : (d:TwoLocal)*x = (n:TwoLocal) := by
      simpa using J6NativeHeightResidue.scalarClearing
        (RingHom.id TwoLocal) x n d hd (by exact hx)
    have hn : (n:NativeProbeRing.Base p)=0 := by
      have e := congrArg (reduceBase p) hEq
      rw [map_mul,h,mul_zero,map_intCast] at e
      exact e.symm
    have hdvd : (2:ℤ)^p ∣ n := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using
        (CharP.intCast_eq_zero_iff (NativeProbeRing.Base p) (2^p) n).mp hn
    have hv : (2:TwoLocal)^p ∣ (n:TwoLocal) := by
      have hmap := map_dvd (Int.castRingHom TwoLocal) hdvd
      simpa only [map_pow,map_ofNat,Int.coe_castRingHom] using hmap
    exact (source_odd_unit d odd).dvd_mul_left.mp (hEq.symm ▸ hv)
  · rintro ⟨y,rfl⟩
    rw [map_mul,map_pow,map_ofNat,NativeProbeRing.base_nilpotent,zero_mul]

theorem reduceBase_kernel (p : ℕ) :
    RingHom.ker (reduceBase p) = Ideal.span ({(2:TwoLocal)^p}:Set TwoLocal) := by
  ext x
  rw [RingHom.mem_ker,Ideal.mem_span_singleton,reduceBase_zero_iff]

/-- Literal quotient equivalence at the printed integer precision p. -/
noncomputable def baseQuotientEquiv (p : ℕ) :
    TwoLocal ⧸ Ideal.span ({(2:TwoLocal)^p}:Set TwoLocal) ≃+* NativeProbeRing.Base p :=
  (Ideal.quotEquivOfEq (reduceBase_kernel p).symm).trans
    ((reduceBase p).quotientKerEquivOfSurjective (reduceBase_surjective p))

theorem baseQuotient_apply (p : ℕ) (x : TwoLocal) :
    baseQuotientEquiv p (Ideal.Quotient.mk _ x) = reduceBase p x := by
  unfold baseQuotientEquiv
  rw [RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Native monic coordinate extraction loses no information on a source
constant. This is the projection used before centered integer lifting. -/
theorem native_constant_projection (p : ℕ) (hp : 0<p) (poly : Polynomial ℤ)
    (hm : poly.Monic) (hd : 0<poly.natDegree) (x : TwoLocal) :
    NativeProbeRing.projectBase p poly hm (reduceNative p poly x) = reduceBase p x :=
  NativeProbeRing.projectBase_left p hp poly hm hd _

#print axioms source_odd_unit
#print axioms reduceBase_surjective
#print axioms reduceBase_zero_iff
#print axioms reduceBase_kernel
#print axioms baseQuotientEquiv
#print axioms baseQuotient_apply
#print axioms native_constant_projection

end J6ZeroTransport