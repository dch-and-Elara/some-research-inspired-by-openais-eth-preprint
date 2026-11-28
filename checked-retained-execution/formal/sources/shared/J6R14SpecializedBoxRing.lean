import J6R9RecursiveProbes
import J9R13PhysicalFusion

/-! Scalar receipt for the actual J9 polynomial evaluations in the
J6 receiving ring. This does not alter any centre, binary address,
precision or higher-order tails. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators
open Polynomial NativeProbeRing DyadicProbeCompiler J6R9Recursive
open J8J9Grouped J8EndToEnd

noncomputable def atZero (q : ℕ) (f : ℤ[X]) (ell : ℕ) (h : 0 < ell) :
    Box f ell q →+* Scalar q f :=
  AdjoinRoot.lift (RingHom.id _) 0 (show
    ((X : (Scalar q f)[X])^ell).eval₂ (RingHom.id _) 0 = 0 from by
      rw [eval₂_pow,eval₂_X,zero_pow h.ne'])

theorem atZero_scalarIn (q : ℕ) (f : ℤ[X]) (ell : ℕ) (h : 0 < ell) (x : Scalar q f) :
    atZero q f ell h (J6ActiveInterpolation.scalarIn q f ell x) = x := by
  change (AdjoinRoot.lift (RingHom.id (Scalar q f)) 0 _) (AdjoinRoot.of _ x) = x
  exact AdjoinRoot.lift_of _

theorem scalarIn_injective (q : ℕ) (f : ℤ[X]) (ell : ℕ) (h : 0 < ell) :
    Function.Injective (J6ActiveInterpolation.scalarIn q f ell) := by
  intro x y hxy
  simpa only [atZero_scalarIn] using congrArg (atZero q f ell h) hxy

noncomputable def evalScalar (q : ℕ) (f : ℤ[X]) (z : Scalar q f) : Source[X] →+* Scalar q f :=
  Polynomial.eval₂RingHom (toScalar q f) (2*z)

noncomputable def evalBox (q : ℕ) (f : ℤ[X]) (ell : ℕ) (z : Scalar q f) : Source[X] →+* Box f ell q :=
  (J6ActiveInterpolation.scalarIn q f ell).comp (evalScalar q f z)

theorem evalBox_proj (q : ℕ) (f : ℤ[X]) (ell : ℕ) (h : 0 < ell)
    (z : Scalar q f) (P : Source[X]) :
    atZero q f ell h (evalBox q f ell z P) = P.eval₂ (toScalar q f) (2*z) :=
  atZero_scalarIn q f ell h _

theorem groupedProbe_box (q : ℕ) (f : ℤ[X]) (ell w : ℕ) {T : Type*}
    (s : Finset T) (pub src : Source[X]) (trg ker : T→Source[X]) (z : Scalar q f) :
    J6ActiveInterpolation.scalarIn q f ell (groupedProbe q f w s pub src trg ker z) =
      (2:Box f ell q)^w * J6ActiveInterpolation.scalarIn q f ell z *
       (evalBox q f ell z pub * evalBox q f ell z src *
         ∑ j ∈ s, evalBox q f ell z (ker j) * evalBox q f ell z (trg j)) := by
  rw [J9R13PhysicalFusion.groupedProbe_eval,map_mul]
  change J6ActiveInterpolation.scalarIn q f ell ((2:Scalar q f)^w*z) *
      evalBox q f ell z (groupedNormalized s pub src trg ker) = _
  simp only [groupedNormalized, map_mul, map_pow, map_ofNat, map_sum]

#print axioms atZero
#print axioms atZero_scalarIn
#print axioms scalarIn_injective
#print axioms evalBox_proj
#print axioms groupedProbe_box
end J6R14SpecializedBox
