import J6R14SpecializedBoxRing
import J6R9PacketLocal
import J6ZeroTransport
import J8PhysicalKernel

/-! Exact source coefficient transport: J9's odd-denominator
localization and the two-local subalgebra used for the actual J6 W
polynomials have the same image. The centre specialization below
uses the real occupied seats and the original cancelled Cauchy entries. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial DyadicProbeCompiler NativeProbeRing J6R9Recursive
open DenominatorBudget J6R9PacketLocal P1DyadicGrid P1DyadicGridBridge

theorem source_denominators_equal : atTwoPrime.primeCompl = odds := by
  ext j
  simp only [atTwoPrime,Ideal.mem_primeCompl_iff,Ideal.mem_span_singleton,odds,
    Submonoid.mem_mk]
  constructor
  · intro h
    refine ⟨j/2,?_⟩
    by_contra he
    apply h
    refine ⟨j/2,?_⟩
    omega
  · rintro ⟨z,hz⟩ ⟨b,hb⟩
    omega

local instance : IsLocalization odds TwoLocal := by
  rw [← source_denominators_equal]
  unfold TwoLocal twoLocalSubalgebra
  infer_instance

noncomputable def twoLocalToSource : TwoLocal ≃ₐ[ℤ] Source :=
  IsLocalization.algEquiv odds _ _

theorem source_rat_agrees (x : TwoLocal) :
    J8EndToEnd.rationalMap (twoLocalToSource x) = twoLocalRat x := by
  have h : J8EndToEnd.rationalMap.comp twoLocalToSource.toRingHom = twoLocalRat :=
    J6ZeroTransport.ringHom_unique _ _
  exact RingHom.congr_fun h x

theorem source_reduce_agrees (q : ℕ) (f : ℤ[X]) (ell : ℕ)
    (hnil : (2 : Box f ell q)^q = 0) :
    ((J6ActiveInterpolation.scalarIn q f ell).comp (toScalar q f)).comp
      twoLocalToSource.toRingHom = J6ZeroTransport.reduceAt q hnil :=
  J6ZeroTransport.ringHom_unique _ _

theorem native_eval_transports (q : ℕ) (f : ℤ[X]) (ell : ℕ)
    (hnil : (2 : Box f ell q)^q = 0) (z : Scalar q f) (P : TwoLocal[X]) :
    J6ActiveInterpolation.scalarIn q f ell
      ((P.map twoLocalToSource.toRingHom).eval₂ (toScalar q f) z) =
      P.eval₂ (J6ZeroTransport.reduceAt q hnil) (J6ActiveInterpolation.scalarIn q f ell z) := by
  rw [Polynomial.hom_eval₂,Polynomial.eval₂_map,source_reduce_agrees q f ell hnil]

section Center
open J8Physical

theorem printed_grid_at_width (a L : ℕ) (hL : L=2^a) :
    grid a = printedGrid L := by
  subst L
  simp [grid,printedGrid,pow₂]

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L) [DecidableEq Packet]

theorem same_native_W_at_extreme (a : ℕ) (hL : L=2^a) (x y : Wire R) :
    centerKernel d x y =
      if (d.seat x).1 = (d.seat y).1 then
        (W a ((L:ℤ)-1) ((d.seat y).2.val-(d.seat x).2.val : ℤ)).eval₂ twoLocalRat 0
      else 0 := by
  have hG := printed_grid_at_width a L hL
  have ht : ((L:ℤ)-1) ∈ grid a := by
    rw [hG]
    simp only [printedGrid,Finset.mem_Ico]
    have := (d.seat x).2.isLt
    omega
  have hk : ((d.seat y).2.val-(d.seat x).2.val : ℤ) ∈ grid a := by
    rw [hG]
    simp only [printedGrid,Finset.mem_Ico]
    have := (d.seat x).2.isLt
    have := (d.seat y).2.isLt
    omega
  unfold centerKernel
  by_cases h : (d.seat x).1=(d.seat y).1
  · rw [if_pos h,if_pos h,W_eval_rat ht hk]
    unfold printedW derivativeProduct
    rw [cauchy_derivative_eval (zero_mem_grid a)]
    simp only [Int.cast_prod,Int.cast_sub,Int.cast_zero,← hG,mul_zero,add_zero]
  · simp [h]
end Center

#print axioms source_denominators_equal
#print axioms twoLocalToSource
#print axioms source_rat_agrees
#print axioms source_reduce_agrees
#print axioms native_eval_transports
#print axioms same_native_W_at_extreme
end J6R14SpecializedBox
