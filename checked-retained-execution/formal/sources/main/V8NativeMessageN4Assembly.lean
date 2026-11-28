import V8NativeMessageN4Private

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4100000

/-! The one-coordinate statement N4 on the original pinned four-copy
formula. The separately supplied bypass is charged its actual rank on
the same matching restriction, not its number of syntactic nodes. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal V8CapacityUnified.U7
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
  {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {i : rootKept F f}
  {A : Type*} [Field A] [LinearOrder A] {γ : A}
  (C : FourCut P i γ)
variable {R O H : Type*} [Field R] [Algebra ℚ R] [CommRing O] [Algebra O R] [Fintype H]
variable (χ : O→+*ZMod 2) (embed : Function.Injective (algebraMap O R))
variable (blocks : H→Block P i R)

def bypassMatrix (bypass : (W→Bool)→R) : Matrix (Fin C.m→Bool) (Fin C.m→Bool) R :=
  Matrix.of fun x y => bypass (restriction C.pairs x y)

include embed in
theorem original_N4_with_bypass (bypass : (W→Bool)→R)
    (correct : ∀ σ : W→Bool, ∃ o : O, algebraMap O R o=(∑ h, sourceValue (blocks h) σ)+bypass σ ∧
      χ o=(nativeCount F reg σ:ZMod 2)) :
    2^C.m≤(∑ h, privateCapacity (blocks h))+(bypassMatrix C bypass).rank := by
  let M := (∑ h, blockMatrix C (blocks h))+bypassMatrix C bypass
  have hM : M.rank=2^C.m := by
    apply matching_lift_rank C.pairs χ embed M
    intro x y
    simpa only [M, Matrix.add_apply,Matrix.sum_apply,blockMatrix,bypassMatrix,Matrix.of_apply] using
      correct (restriction C.pairs x y)
  rw [← hM]
  apply (rank_add_le _ _).trans
  apply Nat.add_le_add_right
  exact (rank_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun h _ => actual_block_rank C (blocks h)))

include embed in
theorem original_N4 (correct : ∀ σ : W→Bool, ∃ o : O,
    algebraMap O R o=(∑ h, sourceValue (blocks h) σ) ∧ χ o=(nativeCount F reg σ:ZMod 2)) :
    2^C.m≤∑ h, privateCapacity (blocks h) := by
  have he : bypassMatrix C (fun _=>(0:R))=(0:Matrix (Fin C.m→Bool) (Fin C.m→Bool) R) := by
    ext x y
    rfl
  have h := original_N4_with_bypass C χ embed blocks (fun _=>0) (fun σ => by
    simpa only [add_zero] using correct σ)
  simpa only [he,Matrix.rank_zero,Nat.add_zero] using h

#print axioms original_N4_with_bypass
#print axioms original_N4
end
end V8NativeMessage.N4
